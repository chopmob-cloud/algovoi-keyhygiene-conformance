#!/usr/bin/env python3
"""Verify a sealed KAF assurance receipt for the keyhygiene battery.

Checks, independently of how the receipt was produced:
  1. the EdDSA seal over the canonical (RFC 8785 JCS) payload verifies under the
     receipt's own published Ed25519 JWK;
  2. the sealed corpus file_sha256 matches the corpus on disk and the signed
     manifest head;
  3. the attested agreement (N languages) equals the distinct passing cells.

Usage: python kaf/kaf_verify.py <receipt.json>
"""
from __future__ import annotations

import base64
import hashlib
import json
import os
import sys

from nacl.signing import VerifyKey
from nacl.exceptions import BadSignatureError

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _b64u_dec(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def canonical(obj) -> bytes:
    import rfc8785
    return rfc8785.dumps(obj)


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: kaf_verify.py <receipt.json>")
        return 2
    with open(sys.argv[1], encoding="utf-8") as fh:
        receipt = json.load(fh)

    failures: list[str] = []
    payload = receipt["payload"]
    seal = receipt["seal"]

    # 1. signature over the canonical payload
    try:
        vk = VerifyKey(_b64u_dec(seal["jwk"]["x"]))
        vk.verify(canonical(payload), base64.b64decode(seal["sig_b64"]))
    except BadSignatureError:
        failures.append("seal signature does not verify under the receipt JWK")
    except (KeyError, ValueError) as e:
        failures.append(f"malformed seal: {e}")

    # 2. corpus binding
    corpus_id = payload["corpus"]["id"]
    corpus_path = os.path.join(HERE, "corpus", corpus_id, corpus_id + ".json")
    try:
        raw = open(corpus_path, "rb").read()
        file_sha = "sha256:" + hashlib.sha256(raw).hexdigest()
        if file_sha != payload["corpus"]["file_sha256"]:
            failures.append(f"corpus file_sha256 {file_sha} != sealed {payload['corpus']['file_sha256']}")
        manifest = json.load(open(corpus_path[:-len('.json')] + ".manifest.json", encoding="utf-8"))
        if manifest["head"].get("file_sha256") != payload["corpus"]["file_sha256"]:
            failures.append("sealed file_sha256 != signed manifest head")
    except OSError as e:
        failures.append(f"cannot bind corpus: {e}")

    # 3. agreement == distinct passing cells
    cells = payload["axes"]["cells"]
    passing = sorted({c["lang"] for c in cells if c["verdict"] == "PASS"})
    if payload["axes"]["agreement"]["languages"] != passing:
        failures.append("attested agreement languages != distinct passing cells")
    if payload["axes"]["cells_passed"] != len(cells) or any(c["verdict"] != "PASS" for c in cells):
        failures.append("receipt attests cells that did not all pass")

    if failures:
        print("RECEIPT: INVALID")
        for f in failures:
            print("  -", f)
        return 1

    a = payload["axes"]["agreement"]
    print("RECEIPT: VALID")
    print(f"  suite      {payload['suite']}  seq {payload['seq']}  sealed_at {payload['sealed_at']}")
    print(f"  seal       Ed25519 kid {seal['kid']} (signature verified)")
    print(f"  corpus     {payload['corpus']['file_sha256']} (matches disk + signed head)")
    print(f"  agreement  full {a['independent_runners']}-way byte-for-byte consensus over {a['cases']} cases")
    print(f"  cells      {payload['axes']['cells_passed']}/{payload['axes']['cells_total']} runtimes PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
