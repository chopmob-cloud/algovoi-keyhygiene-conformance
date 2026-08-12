#!/usr/bin/env python3
"""Generate the keyhygiene_v0 conformance corpus.

Two sections, verdicts computed by tools/oracle.py (the reference decision
surface) and frozen. Big integers are serialised as DECIMAL STRINGS so every
target language parses them into its own big-integer type without loss.

  primality            : candidate integers with ground-truth prime/composite
                         (BPSW). Composites carry a nontrivial factorisation so
                         the KAT gate can re-multiply and confirm compositeness
                         without trusting any primality test. Includes the
                         adversarial strong-pseudoprime set that fools naive
                         fixed-base Miller-Rabin.
  rsa_modulus_hygiene  : RSA public keys (n, e) with accept/reject under the
                         CA/Browser-Forum-tracking policy in oracle.py.

Deterministic: seeded RNG, no wall clock, so regeneration is byte-stable.

Run: python tools/gen_keyhygiene_v0.py
"""
from __future__ import annotations

import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_DIR = os.path.join(ROOT, "corpus", "keyhygiene_v0")

# Documented smallest strong pseudoprimes: composite, but a strong probable
# prime to EVERY base in `bases`, with no factor small enough for light trial
# division to catch relative to that base set. These are the adversarial core.
ADVERSARIAL_SPSP = [
    (2047, [23, 89], [2], "smallest strong pseudoprime to base 2"),
    (1373653, [829, 1657], [2, 3], "smallest spsp to bases 2,3"),
    (25326001, [2251, 11251], [2, 3, 5], "smallest spsp to bases 2,3,5"),
    (3215031751, [151, 751, 28351], [2, 3, 5, 7], "smallest spsp to bases 2,3,5,7"),
]

CARMICHAEL = [
    (561, [3, 11, 17]),
    (1105, [5, 13, 17]),
    (1729, [7, 13, 19]),
    (41041, [7, 11, 13, 41]),
    (825265, [5, 7, 17, 19, 73]),
]


def _prime_case(n: int, note: str) -> dict:
    assert oracle.is_prime(n), f"{n} must be prime"
    return {"value": str(n), "expect_prime": True, "factors": [], "note": note}


def _composite_case(n: int, factors: list[int], note: str) -> dict:
    prod = 1
    for f in factors:
        prod *= f
    assert prod == n, f"factors of {n} do not multiply back ({prod})"
    assert all(f > 1 for f in factors), "trivial factor"
    assert not oracle.is_prime(n), f"{n} must be composite"
    return {"value": str(n), "expect_prime": False,
            "factors": [str(f) for f in factors], "note": note}


def build_primality(rng: random.Random) -> list[dict]:
    cases: list[dict] = []
    # genuine primes, all below the MR12 soundness bound so the KAT anchor holds
    for p, note in [(2, "smallest prime"), (3, "prime"), (97, "prime"),
                    (7919, "prime"), (1000003, "prime ~2^20"),
                    (2147483647, "Mersenne prime 2^31-1")]:
        cases.append(_prime_case(p, note))
    # a larger prime still under the bound (~2^70)
    big_prime = oracle.next_prime(rng.getrandbits(70) | (1 << 69))
    assert big_prime < oracle.MR12_SOUND_BOUND
    cases.append(_prime_case(big_prime, "prime ~2^70 (under MR12 bound)"))

    # trivial composites
    for n, f in [(15, [3, 5]), (21, [3, 7]), (100, [2, 2, 5, 5])]:
        cases.append(_composite_case(n, f, "small composite"))

    # Carmichael numbers: Fermat-pseudoprime to every coprime base
    for n, f in CARMICHAEL:
        cases.append(_composite_case(n, f, "Carmichael number"))

    # THE adversarial set: strong pseudoprimes that fool naive fixed-base MR
    for n, f, bases, note in ADVERSARIAL_SPSP:
        c = _composite_case(n, f, note)
        c["fools_fixed_base_mr"] = bases
        cases.append(c)

    # perfect powers (trivially factorable modulus shape)
    for base, exp in [(1009, 2), (2, 61), (3, 40)]:
        n = base ** exp
        cases.append(_composite_case(n, [base] * exp, f"perfect power {base}^{exp}"))

    # a large semiprime (correctly composite, factors recorded)
    p = oracle.gen_prime(128, rng)
    q = oracle.gen_prime(128, rng)
    cases.append(_composite_case(p * q, sorted([p, q]), "256-bit semiprime"))
    return cases


def _rsa_prime(bits: int, rng: random.Random) -> int:
    """RSA prime with the top TWO bits set, so a product of two of them lands on
    exactly 2*bits (standard keygen practice)."""
    while True:
        cand = rng.getrandbits(bits) | (3 << (bits - 2)) | 1
        if oracle.is_prime(cand):
            return cand


def _rsa_case(n: int, e: int, note: str) -> dict:
    accept, reason = oracle.rsa_modulus_verdict(n, e)
    return {"n": str(n), "e": e, "expect_accept": accept, "reason": reason,
            "bits": n.bit_length(), "note": note}


def build_rsa(rng: random.Random) -> list[dict]:
    cases: list[dict] = []
    # valid controls at each allowed modulus size
    for bits in (2048, 3072, 4096):
        half = bits // 2
        p = _rsa_prime(half, rng)
        while True:
            q = _rsa_prime(half, rng)
            n = p * q
            if n.bit_length() == bits and abs(p - q) > (1 << (half - 8)):
                break
        c = _rsa_case(n, 65537, f"valid {bits}-bit modulus, e=65537")
        assert c["expect_accept"], (bits, c["reason"])
        cases.append(c)

    # e = 3 valid control (allowed by policy)
    p = _rsa_prime(1024, rng)
    while True:
        q = _rsa_prime(1024, rng)
        n = p * q
        if n.bit_length() == 2048 and abs(p - q) > (1 << 1016):
            break
    cases.append(_rsa_case(n, 3, "valid 2048-bit modulus, e=3"))

    # --- reject classes ---
    # close primes (|p-q| small): Fermat-factorable
    p = _rsa_prime(1024, rng)
    q = oracle.next_prime(p + 2)
    cases.append(_rsa_case(p * q, 65537, "close primes (Fermat-factorable)"))

    # small factor
    p = _rsa_prime(1024, rng)
    cases.append(_rsa_case(3 * p, 65537, "modulus with small factor 3"))

    # perfect-power modulus
    p = _rsa_prime(1024, rng)
    cases.append(_rsa_case(p * p, 65537, "perfect-power modulus p^2"))

    # disallowed bit length (2047)
    while True:
        p = _rsa_prime(1024, rng)
        q = _rsa_prime(1023, rng)
        n = p * q
        if n.bit_length() == 2047:
            break
    cases.append(_rsa_case(n, 65537, "disallowed bit length 2047"))

    # disallowed exponent (even)
    p = _rsa_prime(1024, rng)
    while True:
        q = _rsa_prime(1024, rng)
        n = p * q
        if n.bit_length() == 2048 and abs(p - q) > (1 << 1016):
            break
    cases.append(_rsa_case(n, 4, "even public exponent"))
    return cases


def build_batch(rng: random.Random) -> list[dict]:
    """A SET of RSA moduli, some sharing a prime (batch-GCD / Mining-your-Ps-and-Qs).
    Per-key verdict = shares a prime with another key in the set."""
    shared_p = oracle.gen_prime(512, rng)
    shared_r = oracle.gen_prime(512, rng)
    qa, qb = oracle.gen_prime(512, rng), oracle.gen_prime(512, rng)
    qe, qf = oracle.gen_prime(512, rng), oracle.gen_prime(512, rng)
    ind1 = oracle.gen_prime(512, rng) * oracle.gen_prime(512, rng)
    ind2 = oracle.gen_prime(512, rng) * oracle.gen_prime(512, rng)

    raw = [
        (shared_p * qa, str(shared_p), "shares prime P with key #1"),
        (shared_p * qb, str(shared_p), "shares prime P with key #0"),
        (ind1, None, "independent key"),
        (shared_r * qe, str(shared_r), "shares prime R with key #5"),
        (shared_r * qf, str(shared_r), "shares prime R with key #3"),
        (ind2, None, "independent key"),
    ]
    moduli = [n for n, _, _ in raw]
    verdicts = oracle.batch_common_factor_verdicts(moduli)
    cases = []
    for (n, shared_prime, note), shares in zip(raw, verdicts):
        c = {"n": str(n), "shares_factor": shares, "note": note}
        if shared_prime is not None:
            assert shares and n % int(shared_prime) == 0
            c["shared_prime"] = shared_prime  # crafted weak key; not a secret
        cases.append(c)
    return cases


def build_ec(rng: random.Random) -> list[dict]:
    """EC public points on the prime-order curves P-256, P-384, secp256k1:
    valid on-curve points, off-curve points, and out-of-range coordinates."""
    cases = []
    for curve in ("p256", "p384", "secp256k1"):
        c = oracle.EC_CURVES[curve]
        p = c["p"]
        # valid: G and a couple of genuine multiples
        for k, note in [(1, "generator G"), (2, "2*G"), (rng.randint(3, 1 << 40), "k*G")]:
            x, y = oracle.ec_point_mul(curve, k)
            case = {"curve": curve, "x": str(x), "y": str(y), "expect_valid": True,
                    "reason": "ok", "note": f"valid point {note}"}
            assert oracle.ec_key_verdict(curve, x, y) == (True, "ok")
            cases.append(case)
        # off-curve: G with y perturbed
        gx, gy = c["gx"], (c["gy"] + 1) % p
        cases.append({"curve": curve, "x": str(gx), "y": str(gy), "expect_valid": False,
                      "reason": "not_on_curve", "note": "off-curve (perturbed y)"})
        # out-of-range: x = p
        cases.append({"curve": curve, "x": str(p), "y": str(c["gy"]), "expect_valid": False,
                      "reason": "coordinate_out_of_range", "note": "x == p (out of range)"})
    return cases


def build_roca(rng: random.Random) -> list[dict]:
    """ROCA (CVE-2017-15361) fingerprint: moduli whose both primes are Infineon-
    structured (p ≡ 65537^a mod M) carry the fingerprint; normal moduli do not."""
    cases = []
    for i in range(3):
        p = oracle.gen_roca_prime(512, rng)
        q = oracle.gen_roca_prime(512, rng)
        n = p * q
        assert oracle.roca_fingerprint_verdict(n), "structured modulus must be positive"
        cases.append({"n": str(n), "roca_vulnerable": True,
                      "note": f"ROCA-structured modulus #{i} (both primes 65537^a mod M)"})
    made = 0
    while made < 3:
        n = oracle.gen_prime(512, rng) * oracle.gen_prime(512, rng)
        if not oracle.roca_fingerprint_verdict(n):
            cases.append({"n": str(n), "roca_vulnerable": False,
                          "note": "normal RSA modulus (fingerprint-negative)"})
            made += 1
    return cases


def main() -> int:
    rng = random.Random(0xA1601)  # fixed seed: vectors are public, reproducible
    corpus = {
        "name": "keyhygiene_v0",
        "description": "Key-hygiene & primality conformance battery. Given a "
                       "candidate integer or an RSA public key, reproduce the "
                       "reference accept/reject verdict byte-for-byte.",
        "policy": {
            "primality_ground_truth": "Baillie-PSW",
            "mr12_sound_bound": str(oracle.MR12_SOUND_BOUND),
            "rsa_allowed_bits": sorted(oracle.BR_ALLOWED_BITS),
            "rsa_allowed_e": sorted(oracle.BR_ALLOWED_E),
            "rsa_policy_basis": "CA/Browser Forum Baseline Requirements (tracked)",
            "roca_generator": oracle.ROCA_GENERATOR,
            "roca_primes": oracle.ROCA_PRIMES,
        },
        "primality": build_primality(rng),
        "rsa_modulus_hygiene": build_rsa(rng),
        "batch_common_factor": build_batch(rng),
        "ec_key_hygiene": build_ec(rng),
        "roca_fingerprint": build_roca(rng),
    }
    os.makedirs(OUT_DIR, exist_ok=True)
    out = os.path.join(OUT_DIR, "keyhygiene_v0.json")
    # newline="\n": write LF regardless of host OS, so the signed byte digest is
    # stable and matches the repo (git normalises to LF via .gitattributes).
    with open(out, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(corpus, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    print(f"wrote {out}")
    total = 0
    for name, cases in corpus.items():
        if isinstance(cases, list):
            print(f"  {name}: {len(cases)}")
            total += len(cases)
    print(f"  total cases: {total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
