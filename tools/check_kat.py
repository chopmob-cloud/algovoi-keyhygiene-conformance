#!/usr/bin/env python3
"""Independent known-answer (KAT) gate for keyhygiene_v0.

N-way consensus proves the runners AGREE; it cannot rule out a systematic error
shared by the generator and every runner. This gate closes that two ways:

  1. Signed integrity: the corpus bytes must hash to the file_sha256 in the
     signed manifest head, and the head's EdDSA compact-JWS signature must verify
     under the published signer JWK (forgery-resistant, not just a digest match).
  2. Independent anchors, computed WITHOUT the generator's primality test:
       - every composite in `primality` must have its recorded factors multiply
         back to the value (independent proof of compositeness);
       - every prime in `primality` (all below the MR12 soundness bound) must
         pass deterministic Miller-Rabin over the first twelve prime bases, a
         method sound in that range and distinct from the generator's structural
         path;
       - every RSA case's recorded reason must be re-derivable by an independent
         structural check on the modulus.

Fail-closed: any mismatch, a missing/invalid signature, or zero anchors exits
non-zero.

Run: ALGOVOI_LOCAL_SRC=/path/to/algovoi-corpus-cm/src python tools/check_kat.py [corpus.json]
"""
from __future__ import annotations

import base64
import hashlib
import json
import os
import sys

for _d in os.environ.get("ALGOVOI_LOCAL_SRC", "").split(os.pathsep):
    if _d and _d not in sys.path:
        sys.path.insert(0, _d)

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import oracle  # noqa: E402

CORPUS = (sys.argv[1] if len(sys.argv) > 1
          else os.environ.get("ALGOVOI_KEYHYGIENE")
          or os.path.join(REPO, "corpus", "keyhygiene_v0", "keyhygiene_v0.json"))
MANIFEST = CORPUS[:-len(".json")] + ".manifest.json"


def _b64u(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def verify_signed_head(manifest: dict, corpus_file_sha: str) -> list[str]:
    out: list[str] = []
    jws = manifest.get("head_jws")
    signers = manifest.get("signers") or []
    if not jws or not signers:
        return ["manifest is not signed (no head_jws / signer)"]
    try:
        from nacl.signing import VerifyKey
        from nacl.exceptions import BadSignatureError
    except ImportError:
        return ["PyNaCl required to verify the signed head (pip install pynacl)"]
    try:
        h_b64, p_b64, s_b64 = jws.split(".")
        pk = _b64u(signers[0]["jwk"]["x"])
        VerifyKey(pk).verify(f"{h_b64}.{p_b64}".encode("ascii"), _b64u(s_b64))
    except (ValueError, KeyError) as e:
        return [f"head_jws is malformed: {e}"]
    except BadSignatureError:
        return ["head_jws EdDSA signature does not verify under the signer JWK"]
    payload = json.loads(_b64u(p_b64))
    if payload != manifest.get("head"):
        out.append("manifest head object does not match the signed head_jws payload")
    if payload.get("file_sha256") != corpus_file_sha:
        out.append(f"signed head binds file_sha256 {payload.get('file_sha256')} != corpus {corpus_file_sha}")
    return out


def anchor_primality(corpus: dict) -> list[str]:
    fails, anchored = [], 0
    for i, c in enumerate(corpus.get("primality", [])):
        n = int(c["value"])
        if c["expect_prime"]:
            if n >= oracle.MR12_SOUND_BOUND:
                fails.append(f"primality[{i}] prime {n} is above the MR12 anchor bound")
                continue
            if not oracle.mr_fixed_base(n, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]):
                fails.append(f"primality[{i}] anchor: deterministic MR12 says {n} is composite")
            anchored += 1
        else:
            factors = [int(f) for f in c.get("factors", [])]
            if len(factors) < 2:
                fails.append(f"primality[{i}] composite {n} carries no factorisation anchor")
                continue
            prod = 1
            for f in factors:
                prod *= f
            if prod != n or any(f <= 1 for f in factors):
                fails.append(f"primality[{i}] anchor: factors do not multiply back to {n}")
            anchored += 1
    if anchored == 0:
        fails.append("no primality anchors present")
    return fails


def anchor_rsa(corpus: dict) -> list[str]:
    fails, anchored = [], 0
    for i, c in enumerate(corpus.get("rsa_modulus_hygiene", [])):
        n, e, reason = int(c["n"]), int(c["e"]), c["reason"]
        # re-derive the structural fact behind the recorded reason, independently
        if reason == "modulus_perfect_power":
            ok = oracle.is_perfect_power(n)
        elif reason == "modulus_small_factor":
            ok = oracle.smallest_factor(n) is not None
        elif reason == "modulus_close_primes":
            ok = oracle.fermat_close_factor(n) is not None
        elif reason == "modulus_bit_length_not_allowed":
            ok = n.bit_length() not in oracle.BR_ALLOWED_BITS
        elif reason in ("public_exponent_not_allowed", "public_exponent_invalid"):
            ok = e not in oracle.BR_ALLOWED_E or e < 3 or e % 2 == 0
        elif reason == "modulus_not_odd_or_too_small":
            ok = n <= 3 or n % 2 == 0
        elif reason == "ok":
            ok = (not oracle.is_perfect_power(n) and oracle.smallest_factor(n) is None
                  and oracle.fermat_close_factor(n) is None
                  and n.bit_length() in oracle.BR_ALLOWED_BITS and e in oracle.BR_ALLOWED_E)
        else:
            fails.append(f"rsa[{i}] unknown reason {reason!r}")
            continue
        if not ok:
            fails.append(f"rsa[{i}] anchor: reason {reason!r} not independently reproducible for n({c['bits']}b)")
        anchored += 1
    if anchored == 0:
        fails.append("no RSA anchors present")
    return fails


def anchor_batch(corpus: dict) -> list[str]:
    fails, anchored = [], 0
    section = corpus.get("batch_common_factor", [])
    moduli = [int(c["n"]) for c in section]
    for i, c in enumerate(section):
        n = int(c["n"])
        if c["shares_factor"]:
            # independent proof: the provided shared prime really is a common factor
            sp = c.get("shared_prime")
            if not sp:
                fails.append(f"batch[{i}] shares_factor but no shared_prime anchor")
                continue
            sp = int(sp)
            others = [m for j, m in enumerate(moduli) if j != i and m % sp == 0]
            if not (sp > 1 and n % sp == 0 and others):
                fails.append(f"batch[{i}] anchor: shared_prime not a genuine common factor")
        else:
            # independent proof: gcd with every other modulus is 1
            from math import gcd
            if any(gcd(n, m) != 1 for j, m in enumerate(moduli) if j != i):
                fails.append(f"batch[{i}] anchor: marked independent but shares a factor")
        anchored += 1
    if section and anchored == 0:
        fails.append("no batch anchors present")
    return fails


def anchor_ec(corpus: dict) -> list[str]:
    fails, anchored = [], 0
    for i, c in enumerate(corpus.get("ec_key_hygiene", [])):
        valid, reason = oracle.ec_key_verdict(c["curve"], int(c["x"]), int(c["y"]))
        if valid != c["expect_valid"] or reason != c["reason"]:
            fails.append(f"ec[{i}] anchor: independent on-curve check gives ({valid},{reason}) "
                         f"!= recorded ({c['expect_valid']},{c['reason']})")
        anchored += 1
    return fails


def anchor_roca(corpus: dict) -> list[str]:
    fails, anchored = [], 0
    primes = corpus.get("policy", {}).get("roca_primes")
    for i, c in enumerate(corpus.get("roca_fingerprint", [])):
        # independent re-derivation of the fingerprint from n and the published
        # prime set: n mod pf is a power of 65537 for every pf.
        got = oracle.roca_fingerprint_verdict(int(c["n"]))
        if primes and set(primes) != set(oracle.ROCA_PRIMES):
            fails.append(f"roca[{i}] anchor: corpus roca_primes != oracle ROCA_PRIMES")
        if got != c["roca_vulnerable"]:
            fails.append(f"roca[{i}] anchor: independent fingerprint {got} != recorded {c['roca_vulnerable']}")
        anchored += 1
    return fails


def main() -> int:
    failures: list[str] = []
    raw = open(CORPUS, "rb").read()
    corpus = json.loads(raw)
    file_sha = "sha256:" + hashlib.sha256(raw).hexdigest()

    try:
        manifest = json.load(open(MANIFEST, encoding="utf-8"))
        recorded = manifest["head"].get("file_sha256")
        if recorded != file_sha:
            failures.append(f"corpus digest drift: manifest {recorded} != actual {file_sha}")
        failures.extend(verify_signed_head(manifest, file_sha))
    except (OSError, KeyError, json.JSONDecodeError) as e:
        failures.append(f"cannot read signed manifest head: {e}")

    failures.extend(anchor_primality(corpus))
    failures.extend(anchor_rsa(corpus))
    failures.extend(anchor_batch(corpus))
    failures.extend(anchor_ec(corpus))
    failures.extend(anchor_roca(corpus))

    if failures:
        print("KAT: FAIL")
        for f in failures:
            print("  -", f)
        return 1

    counts = {s: len(corpus.get(s, [])) for s in
              ("primality", "rsa_modulus_hygiene", "batch_common_factor",
               "ec_key_hygiene", "roca_fingerprint")}
    print("KAT: PASS")
    print(f"  signed head        head_jws EdDSA signature verified under signer JWK")
    print(f"  corpus integrity   {file_sha} (matches signed head)")
    print(f"  primality anchors  {counts['primality']} (composites re-multiplied, primes MR12-confirmed)")
    print(f"  rsa anchors        {counts['rsa_modulus_hygiene']} (each reason independently re-derived)")
    print(f"  batch anchors      {counts['batch_common_factor']} (shared prime / gcd re-derived)")
    print(f"  ec anchors         {counts['ec_key_hygiene']} (on-curve independently re-checked)")
    print(f"  roca anchors       {counts['roca_fingerprint']} (fingerprint independently re-derived)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
