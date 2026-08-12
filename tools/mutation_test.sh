#!/usr/bin/env bash
# Mutation meta-test: prove the byte-for-byte gate has teeth.
#
# A consensus battery is only meaningful if the runners genuinely COMPUTE each
# verdict rather than echo the corpus's expected value. This flips one expected
# verdict in each section, feeds the mutated corpus to every present runner (KAT
# gate skipped, since it would reject the edit first), and requires the consensus
# to go NOT GREEN each time. A mutation the runners do NOT catch is a fail-open /
# echoing runner.
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
CORPUS="${ALGOVOI_KEYHYGIENE:-$HERE/corpus/keyhygiene_v0/keyhygiene_v0.json}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
PY="$(command -v python3 || command -v python || true)"

# each mutation: "section:index:field:op"
MUTATIONS=(
  "primality:0:expect_prime:flip"            # lie about a primality verdict
  "rsa_modulus_hygiene:0:expect_accept:flip" # lie about an RSA accept
)

mutate() {
  "$PY" - "$CORPUS" "$TMP/mut.json" "$1" <<'PY'
import json, sys
src, dst, spec = sys.argv[1], sys.argv[2], sys.argv[3]
section, idx, field, op = spec.split(":")
d = json.load(open(src, encoding="utf-8"))
case = d[section][int(idx)]
cur = case.get(field)
case[field] = (not cur) if op == "flip" and isinstance(cur, bool) else cur
json.dump(d, open(dst, "w", encoding="utf-8"), ensure_ascii=False)
print(f"{section}[{idx}].{field}: {cur!r} -> {case[field]!r}")
PY
}

echo "Mutation meta-test: every flipped expectation must be caught (NOT GREEN)"
echo "================================================================"
overall=0
for spec in "${MUTATIONS[@]}"; do
  label="$(mutate "$spec")"
  out="$(SKIP_KAT=1 ALGOVOI_KEYHYGIENE="$TMP/mut.json" bash "$HERE/tools/run_consensus.sh" --require 1 2>&1)"
  if printf '%s' "$out" | grep -q "NOT GREEN"; then
    caught="$(printf '%s' "$out" | sed -n 's/.*consensus FAIL in:\s*//p')"
    n="$(printf '%s' "$caught" | wc -w)"
    printf "  CAUGHT  %-45s by %s runner(s):%s\n" "$label" "$n" "$caught"
  else
    printf "  MISSED  %-45s -- runners did NOT catch this mutation!\n" "$label"
    overall=1
  fi
done
echo "================================================================"
if [ "$overall" = 0 ]; then
  echo "RESULT: PASS -- every mutation was caught; the gate is not vacuous"
else
  echo "RESULT: FAIL -- a mutation slipped through (fail-open / echoing runner)"
fi
exit $overall
