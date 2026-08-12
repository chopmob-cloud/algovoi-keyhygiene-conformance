#!/usr/bin/env python3
"""Python reference runner for the keyhygiene battery.

Reads the frozen corpus and, for every case, INDEPENDENTLY computes the verdict
from the inputs (its own Baillie-PSW primality and RSA hygiene detectors) and
compares it to the frozen expectation. Exits 0 iff every case matches, so
"runner passes" == "runner reproduces the reference verdict byte-for-byte".

The verdict logic lives in tools/oracle.py, the reference decision surface that
the other eleven language runners port. This runner is that reference.

Usage: python runners/python/verify_py.py [corpus.json]
"""
from __future__ import annotations

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import oracle  # noqa: E402

DEFAULT = os.path.join(ROOT, "corpus", "keyhygiene_v0", "keyhygiene_v0.json")


def main() -> int:
    path = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("ALGOVOI_KEYHYGIENE", DEFAULT)
    with open(path, encoding="utf-8") as fh:
        corpus = json.load(fh)

    failures: list[str] = []

    for i, c in enumerate(corpus.get("primality", [])):
        n = int(c["value"])
        got = oracle.is_prime(n)
        if got != c["expect_prime"]:
            failures.append(f"primality[{i}] {c['note']}: got prime={got} want {c['expect_prime']}")

    for i, c in enumerate(corpus.get("rsa_modulus_hygiene", [])):
        n, e = int(c["n"]), int(c["e"])
        accept, reason = oracle.rsa_modulus_verdict(n, e)
        if accept != c["expect_accept"] or reason != c["reason"]:
            failures.append(
                f"rsa_modulus_hygiene[{i}] {c['note']}: got ({accept},{reason}) "
                f"want ({c['expect_accept']},{c['reason']})")

    batch = corpus.get("batch_common_factor", [])
    if batch:
        moduli = [int(c["n"]) for c in batch]
        verdicts = oracle.batch_common_factor_verdicts(moduli)
        for i, (c, got) in enumerate(zip(batch, verdicts)):
            if got != c["shares_factor"]:
                failures.append(f"batch_common_factor[{i}] {c['note']}: got shares={got} want {c['shares_factor']}")

    for i, c in enumerate(corpus.get("ec_key_hygiene", [])):
        valid, reason = oracle.ec_key_verdict(c["curve"], int(c["x"]), int(c["y"]))
        if valid != c["expect_valid"] or reason != c["reason"]:
            failures.append(
                f"ec_key_hygiene[{i}] {c['note']}: got ({valid},{reason}) "
                f"want ({c['expect_valid']},{c['reason']})")

    total = sum(len(corpus.get(s, [])) for s in
                ("primality", "rsa_modulus_hygiene", "batch_common_factor", "ec_key_hygiene"))
    if failures:
        print(f"FAIL: {len(failures)}/{total} cases diverged")
        for f in failures[:20]:
            print("  -", f)
        return 1
    print(f"python: {total}/{total} cases matched")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
