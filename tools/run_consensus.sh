#!/usr/bin/env bash
# N-way consensus driver for the keyhygiene battery.
#
# Runs every language runner against the ONE frozen, signed corpus and requires
# that all of them reproduce it. Each runner exits 0 iff it matched every case;
# the frozen corpus is the shared oracle, so every runner passing means all
# runners agree byte-for-byte per case. Fail-closed:
#
#   - a runner whose toolchain is missing is ABSENT (it shrinks N);
#   - a runner that ran but did not fully match is a consensus FAIL;
#   - fewer than --require runners present -> NOT GREEN;
#   - any present runner FAIL              -> NOT GREEN.
#
# Usage:  tools/run_consensus.sh [--require N]
# Env:    ALGOVOI_KEYHYGIENE  corpus path (default: repo corpus)
#         ALGOVOI_LOCAL_SRC   algovoi-corpus-cm src (for the KAT signature gate)
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
CORPUS="${ALGOVOI_KEYHYGIENE:-$HERE/corpus/keyhygiene_v0/keyhygiene_v0.json}"
REQUIRE=12
[ "${1:-}" = "--require" ] && REQUIRE="${2:-12}"

LANGS=(python typescript go rust c java kotlin scala dotnet ruby php elixir)

have() { command -v "$1" >/dev/null 2>&1; }
PY="$(command -v python3 || command -v python || true)"

run_lang() {
  case "$1" in
    python)
      [ -n "$PY" ] || { echo "ABSENT: no python"; return; }
      "$PY" "$HERE/runners/python/verify_py.py" "$CORPUS" >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    typescript)
      have node || { echo "ABSENT: no node"; return; }
      node "$HERE/runners/typescript/verify_ts.mjs" "$CORPUS" >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    go)
      have go || { echo "ABSENT: no go"; return; }
      [ -f "$HERE/runners/go/verify_go.go" ] || { echo "ABSENT: go runner not present"; return; }
      ( cd "$HERE/runners/go" && GOTOOLCHAIN=local go run verify_go.go "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    rust)
      have cargo || { echo "ABSENT: no cargo"; return; }
      [ -f "$HERE/runners/rust/Cargo.toml" ] || { echo "ABSENT: rust runner not present"; return; }
      ( cd "$HERE/runners/rust" && cargo run -q -- "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    c)
      { have cc && pkg-config --exists jansson 2>/dev/null; } || { echo "ABSENT: no cc/jansson"; return; }
      [ -f "$HERE/runners/c/verify.c" ] || { echo "ABSENT: c runner not present"; return; }
      ( cd "$HERE/runners/c" && cc -O2 -w -o verify verify.c $(pkg-config --cflags --libs jansson) -lgmp && ./verify "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    java)
      have javac && have java || { echo "ABSENT: no jdk"; return; }
      [ -f "$HERE/runners/java/Verify.java" ] || { echo "ABSENT: java runner not present"; return; }
      [ -n "${KEYHYGIENE_JSON_JAR:-}" ] || { echo "ABSENT: set KEYHYGIENE_JSON_JAR to the org.json jar"; return; }
      ( cd "$HERE/runners/java" && javac -cp "$KEYHYGIENE_JSON_JAR" Verify.java && java -cp ".:$KEYHYGIENE_JSON_JAR" Verify "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    kotlin)
      have kotlinc && have java || { echo "ABSENT: no kotlinc/java"; return; }
      [ -f "$HERE/runners/kotlin/Verify.kt" ] || { echo "ABSENT: kotlin runner not present"; return; }
      [ -n "${KEYHYGIENE_JSON_JAR:-}" ] || { echo "ABSENT: set KEYHYGIENE_JSON_JAR to the org.json jar"; return; }
      ( cd "$HERE/runners/kotlin" && kotlinc Verify.kt -cp "$KEYHYGIENE_JSON_JAR" -include-runtime -d v.jar >/dev/null 2>&1 && java -cp "v.jar:$KEYHYGIENE_JSON_JAR" VerifyKt "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    scala)
      have scala-cli || { echo "ABSENT: no scala-cli"; return; }
      [ -f "$HERE/runners/scala/verify.scala" ] || { echo "ABSENT: scala runner not present"; return; }
      ( cd "$HERE/runners/scala" && scala-cli run --server=false verify.scala -- "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    dotnet)
      have dotnet || { echo "ABSENT: no dotnet"; return; }
      [ -f "$HERE/runners/dotnet/verify.csproj" ] || { echo "ABSENT: dotnet runner not present"; return; }
      ( cd "$HERE/runners/dotnet" && DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_NOLOGO=1 dotnet run -c Release --verbosity quiet -- "$CORPUS" ) >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    ruby)
      have ruby || { echo "ABSENT: no ruby"; return; }
      [ -f "$HERE/runners/ruby/verify.rb" ] || { echo "ABSENT: ruby runner not present"; return; }
      ruby "$HERE/runners/ruby/verify.rb" "$CORPUS" >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    php)
      have php || { echo "ABSENT: no php"; return; }
      [ -f "$HERE/runners/php/verify.php" ] || { echo "ABSENT: php runner not present"; return; }
      php "$HERE/runners/php/verify.php" "$CORPUS" >/dev/null 2>&1 && echo PASS || echo FAIL ;;
    elixir)
      have elixir || { echo "ABSENT: no elixir"; return; }
      [ -f "$HERE/runners/elixir/verify.exs" ] || { echo "ABSENT: elixir runner not present"; return; }
      elixir "$HERE/runners/elixir/verify.exs" "$CORPUS" >/dev/null 2>&1 && echo PASS || echo FAIL ;;
  esac
}

echo "N-way consensus over keyhygiene (require ${REQUIRE})"
echo "corpus: $CORPUS"
echo "----------------------------------------------------------------"

# KAT integrity gate (fail-closed): the corpus must be the exact signed artifact
# and every verdict must be independently re-derivable, so a systematic error
# shared by the generator and every runner cannot pass as consensus. SKIP_KAT=1
# is used only by mutation_test.sh (which feeds a deliberately mutated corpus).
if [ "${SKIP_KAT:-0}" != 1 ] && [ -n "$PY" ]; then
  if ! "$PY" "$HERE/tools/check_kat.py" "$CORPUS"; then
    echo "RESULT: NOT GREEN -- KAT integrity gate failed"
    exit 1
  fi
  echo "----------------------------------------------------------------"
fi

present=0; passed=0; failed_langs=""
for lang in "${LANGS[@]}"; do
  verdict="$(run_lang "$lang")"
  printf "  %-11s %s\n" "$lang" "$verdict"
  case "$verdict" in
    PASS) present=$((present+1)); passed=$((passed+1)) ;;
    FAIL) present=$((present+1)); failed_langs="$failed_langs $lang" ;;
  esac
done
echo "----------------------------------------------------------------"
echo "present: ${present}/${#LANGS[@]}   passed: ${passed}   require: ${REQUIRE}"

if [ -n "$failed_langs" ]; then
  echo "RESULT: NOT GREEN -- consensus FAIL in:${failed_langs}"
  exit 1
fi
if [ "$present" -lt "$REQUIRE" ]; then
  echo "RESULT: NOT GREEN -- only ${present} implementations present, require ${REQUIRE}"
  exit 1
fi
echo "RESULT: FULL ${present}-WAY CONSENSUS -- every implementation reproduces every case"
exit 0
