#!/bin/bash
# Interleaved A/B on two ways of pinning the divisor sum of lcm (1..n) to a literal:
#   kernel  — Lean's checker filters the primes up to n and takes each logarithm itself
#   factor  — the elaborator supplies the prime powers and the checker verifies them
# Three rounds, order alternating. Reports wall-clock seconds per build of the probe.
set -u
PROBE=HighlyAbundant/SigmaRoutes.lean
N="${1:-169}"

lake build HighlyAbundant.SigmaRoutes > /tmp/deps.log 2>&1 || {
  echo "dependencies failed to build"; tail -5 /tmp/deps.log; exit 1
}

set_route () {
  python3 - "$1" "$N" <<'PY'
import pathlib, re, sys
route, n = sys.argv[1], sys.argv[2]
p = pathlib.Path("HighlyAbundant/SigmaRoutes.lean")
s = p.read_text()
s = re.sub(r"by sigma_route_\w+ \d+", f"by sigma_route_{route} {n}", s)
p.write_text(s)
PY
}

measure () {
  local route="$1" round="$2"
  set_route "$route" || { echo "round$round $route PATCH-FAILED"; return; }
  local start end
  start=$(date +%s.%N)
  if ! lake env lean "$PROBE" > /tmp/route.log 2>&1; then
    echo "round$round $route FAILED"; head -3 /tmp/route.log; return
  fi
  end=$(date +%s.%N)
  echo "round$round $route $(echo "$end - $start" | bc)s"
}

for r in 1 2 3; do
  if [ $((r % 2)) -eq 1 ]; then
    measure kernel "$r"; measure factor "$r"
  else
    measure factor "$r"; measure kernel "$r"
  fi
done
set_route kernel
