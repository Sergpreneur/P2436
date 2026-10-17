#!/bin/sh
set -eu
BASE="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$BASE/.build"
c++ -O3 -std=c++17 -Wall -Wextra -pedantic "$BASE/src/exact_search.cpp" -o "$BASE/.build/exact_search"
python3 "$BASE/verify/verify_witness.py" --small-test 6000
small="$(mktemp -d)"
trap 'rm -rf "$small"' EXIT
"$BASE/.build/exact_search" 6000 "$small/run"
python3 "$BASE/verify/verify_witness.py" --summary "$small/run/run_summary.json" --small-test 2000
