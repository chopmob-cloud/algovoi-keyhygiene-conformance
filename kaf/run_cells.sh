#!/usr/bin/env bash
# KAF cell runner for the keyhygiene battery.
#
# Runs each language's runner against the one frozen, signed corpus inside its
# pinned Docker image, so the byte-for-byte verdict is shown to hold in a clean,
# independent runtime (the KAF "Cells" axis). Each cell installs/builds its deps
# fresh in-container. Per-cell verdict + resolved image digest are written to
# kaf/cells.results.json for sealing.
#
# Env:
#   REPO   repo checkout mounted at /work (default: this repo)
#   CELLS  space-separated cell ids to run (default: all in cells.json)
set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="${REPO:-$HERE}"
CORPUS="corpus/keyhygiene_v0/keyhygiene_v0.json"
CORPUS_IN="/work/$CORPUS"
RESULTS="$HERE/kaf/cells.results.json"

ALL_CELLS="python-3.12-slim node-20-slim go-1.23-bookworm rust-1-slim gcc-14-c temurin-17-java temurin-17-kotlin temurin-17-scala dotnet-sdk-9.0 ruby-3.2-slim php-8.3-cli elixir-1.16-otp26"
CELLS="${CELLS:-$ALL_CELLS}"

image_for() {
  case "$1" in
    python-3.12-slim)  echo "python:3.12-slim" ;;
    node-20-slim)      echo "node:20-slim" ;;
    go-1.23-bookworm)  echo "golang:1.23-bookworm" ;;
    rust-1-slim)       echo "rust:1-slim-bookworm" ;;
    gcc-14-c)          echo "gcc:14-bookworm" ;;
    temurin-17-java|temurin-17-kotlin|temurin-17-scala) echo "eclipse-temurin:17" ;;
    dotnet-sdk-9.0)    echo "mcr.microsoft.com/dotnet/sdk:9.0" ;;
    ruby-3.2-slim)     echo "ruby:3.2-slim" ;;
    php-8.3-cli)       echo "php:8.3-cli" ;;
    elixir-1.16-otp26) echo "elixir:1.16-otp-26" ;;
  esac
}

# the in-container command for each cell (runners take only the corpus path)
cmd_for() {
  case "$1" in
    python-3.12-slim)
      echo 'python /work/runners/python/verify_py.py '"$CORPUS_IN" ;;
    node-20-slim)
      echo 'node /work/runners/typescript/verify_ts.mjs '"$CORPUS_IN" ;;
    go-1.23-bookworm)
      echo 'export GOCACHE=/tmp/gc GOPATH=/tmp/gp HOME=/tmp GO111MODULE=off && go run /work/runners/go/verify_go.go '"$CORPUS_IN" ;;
    rust-1-slim)
      echo 'export CARGO_HOME=/tmp/ch CARGO_TARGET_DIR=/tmp/tgt && cd /work/runners/rust && cargo run -q -- '"$CORPUS_IN" ;;
    gcc-14-c)
      echo 'apt-get update -q >/dev/null && apt-get install -y -q libgmp-dev libjansson-dev pkg-config >/dev/null && cd /tmp && cp /work/runners/c/verify.c . && cc -O2 -w -o v verify.c $(pkg-config --cflags --libs jansson) -lgmp && ./v '"$CORPUS_IN" ;;
    temurin-17-java)
      echo 'apt-get update -q >/dev/null && apt-get install -y -q curl >/dev/null && cd /tmp && cp /work/runners/java/Verify.java . && curl -fsSL https://repo1.maven.org/maven2/org/json/json/20240303/json-20240303.jar -o json.jar && javac -cp json.jar Verify.java && java -cp .:json.jar Verify '"$CORPUS_IN" ;;
    temurin-17-kotlin)
      echo 'apt-get update -q >/dev/null && apt-get install -y -q curl unzip >/dev/null && curl -fsSL -o /tmp/k.zip https://github.com/JetBrains/kotlin/releases/download/v2.0.20/kotlin-compiler-2.0.20.zip && unzip -q /tmp/k.zip -d /opt && cd /tmp && cp /work/runners/kotlin/Verify.kt . && curl -fsSL https://repo1.maven.org/maven2/org/json/json/20240303/json-20240303.jar -o json.jar && /opt/kotlinc/bin/kotlinc Verify.kt -cp json.jar -include-runtime -d v.jar >/dev/null 2>&1 && java -cp v.jar:json.jar VerifyKt '"$CORPUS_IN" ;;
    temurin-17-scala)
      echo 'apt-get update -q >/dev/null && apt-get install -y -q curl >/dev/null && curl -fsLo /tmp/scala-cli.gz https://github.com/VirtusLab/scala-cli/releases/latest/download/scala-cli-x86_64-pc-linux.gz && gzip -df /tmp/scala-cli.gz && chmod +x /tmp/scala-cli && cp /work/runners/scala/verify.scala /tmp/ && cd /tmp && HOME=/tmp /tmp/scala-cli run --server=false verify.scala -- '"$CORPUS_IN" ;;
    dotnet-sdk-9.0)
      echo 'export HOME=/tmp DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_NOLOGO=1 && cd /tmp && cp /work/runners/dotnet/verify.csproj /work/runners/dotnet/Program.cs . && dotnet run -c Release --verbosity quiet -- '"$CORPUS_IN" ;;
    ruby-3.2-slim)
      echo 'ruby /work/runners/ruby/verify.rb '"$CORPUS_IN" ;;
    php-8.3-cli)
      echo 'apt-get update -q >/dev/null && apt-get install -y -q libgmp-dev >/dev/null && docker-php-ext-install -j2 gmp >/dev/null 2>&1; php /work/runners/php/verify.php '"$CORPUS_IN" ;;
    elixir-1.16-otp26)
      echo 'export HOME=/tmp MIX_HOME=/tmp/.mix HEX_HOME=/tmp/.hex && elixir /work/runners/elixir/verify.exs '"$CORPUS_IN" ;;
  esac
}

echo "KAF cells for keyhygiene"
echo "repo: $REPO"
echo "================================================================"
results="[]"
for cell in $CELLS; do
  image="$(image_for "$cell")"
  lang="$(python3 -c "import json; print(next(c['lang'] for c in json.load(open('$HERE/kaf/cells.json'))['cells'] if c['id']=='$cell'))" 2>/dev/null || echo "?")"
  printf "  %-20s %-34s " "$cell" "$image"
  if docker run --rm -v "$REPO":/work:ro "$image" sh -c "$(cmd_for "$cell")" >/tmp/cell_"$cell".log 2>&1; then
    verdict=PASS
  else
    verdict=FAIL
  fi
  digest="$(docker image inspect --format '{{if .RepoDigests}}{{index .RepoDigests 0}}{{else}}{{.Id}}{{end}}' "$image" 2>/dev/null)"
  echo "$verdict"
  [ "$verdict" = FAIL ] && tail -3 /tmp/cell_"$cell".log | sed 's/^/       /'
  results="$(printf '%s' "$results" | python3 -c "import json,sys; a=json.load(sys.stdin); a.append({'cell':'$cell','lang':'$lang','image':'$image','image_digest':'''$digest''','verdict':'$verdict'}); print(json.dumps(a))")"
done
echo "================================================================"
printf '%s' "$results" | python3 -m json.tool > "$RESULTS"
passed="$(printf '%s' "$results" | python3 -c "import json,sys; print(sum(1 for c in json.load(sys.stdin) if c['verdict']=='PASS'))")"
total="$(printf '%s' "$results" | python3 -c "import json,sys; print(len(json.load(sys.stdin)))")"
echo "cells passed: $passed/$total   -> $RESULTS"
[ "$passed" = "$total" ] && [ "$total" -gt 0 ]
