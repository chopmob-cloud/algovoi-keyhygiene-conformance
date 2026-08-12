#!/usr/bin/env python3
"""Demonstrate that the primality section has discriminating power.

A conformance corpus of primality verdicts is only meaningful if a WEAK
implementation actually gets some wrong. This runs a deliberately naive checker
(strong Miller-Rabin to a small fixed base set, the common real-world shortcut)
against the frozen primality section and reports every case where it diverges
from the ground truth. The adversarial strong-pseudoprimes MUST be misclassified
as prime; if they were not, the section would not be exercising anything.

Run: python tools/demo_naive_divergence.py
"""
from __future__ import annotations

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.join(ROOT, "corpus", "keyhygiene_v0", "keyhygiene_v0.json")

def main() -> int:
    corpus = json.load(open(CORPUS, encoding="utf-8"))
    adversarial = [c for c in corpus["primality"] if c.get("fools_fixed_base_mr")]

    print("Each adversarial vector is a composite that is a STRONG pseudoprime to")
    print("its target base set: a naive checker using those bases calls it prime,")
    print("while Baillie-PSW (ground truth) catches it.\n")

    fooled = 0
    for c in adversarial:
        n = int(c["value"])
        bases = c["fools_fixed_base_mr"]
        naive = oracle.mr_fixed_base(n, bases)          # the naive shortcut
        truth = oracle.is_prime(n)                       # Baillie-PSW ground truth
        recorded = c["expect_prime"]
        ok = (naive is True) and (truth is False) and (recorded is False)
        print(f"  n={n}")
        print(f"     naive MR bases {bases}: prime={naive}   BPSW: prime={truth}   "
              f"corpus: prime={recorded}   {'FOOLED' if naive and not truth else '-'}")
        if not ok:
            print(f"  UNEXPECTED: vector did not behave as a discriminating pseudoprime")
            return 1
        fooled += 1

    # a sanity floor: BPSW must never call a true prime composite in this corpus
    for c in corpus["primality"]:
        if c["expect_prime"] and not oracle.is_prime(int(c["value"])):
            print(f"UNEXPECTED: ground truth misclassified a prime {c['value']}")
            return 1

    print(f"\nOK: {fooled}/{len(adversarial)} adversarial pseudoprimes fool a naive "
          f"fixed-base checker; ground truth catches every one. The section discriminates.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
