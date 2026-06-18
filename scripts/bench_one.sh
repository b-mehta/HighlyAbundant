#!/usr/bin/env bash
# Run /usr/bin/time -v on `lake env lean --tstack=$TSTACK <file>` N times,
# emitting one CSV row per run with peak RSS, wall, faults.
#
# Usage: scripts/bench_one.sh <label> <leanfile> [runs]
set -euo pipefail

LABEL="$1"
FILE="$2"
RUNS="${3:-3}"
TSTACK="${TSTACK:-4194304}"
OUT="${OUT:-/tmp/bench.csv}"

if [[ ! -s "$OUT" ]]; then
  echo "label,run,wall_s,user_s,sys_s,peak_rss_kb,major_faults,minor_faults,exit,mem_avail_kb_before" > "$OUT"
fi

for i in $(seq 1 "$RUNS"); do
  mem_before=$(awk '/MemAvailable/ {print $2}' /proc/meminfo)
  tmp=$(mktemp)
  set +e
  /usr/bin/time -v -o "$tmp" \
    lake env lean --tstack="$TSTACK" "$FILE" >/dev/null 2>&1
  exit_code=$?
  set -e

  wall=$(awk -F'): ' '/Elapsed.*wall/ {print $2}' "$tmp")
  user=$(awk -F': '  '/User time/   {print $2}' "$tmp")
  sys=$(awk  -F': '  '/System time/ {print $2}' "$tmp")
  rss=$(awk  -F': '  '/Maximum resident/ {print $2}' "$tmp")
  majf=$(awk -F': '  '/Major.*page faults/ {print $2}' "$tmp")
  minf=$(awk -F': '  '/Minor.*page faults/ {print $2}' "$tmp")

  # wall: convert h:mm:ss(.ss) or m:ss(.ss) to seconds
  wall_s=$(awk -v w="$wall" 'BEGIN {
    n=split(w,a,":"); s=0;
    if (n==1) s=a[1]; else if (n==2) s=a[1]*60+a[2]; else s=a[1]*3600+a[2]*60+a[3];
    print s
  }')

  echo "$LABEL,$i,$wall_s,$user,$sys,$rss,$majf,$minf,$exit_code,$mem_before" >> "$OUT"
  echo "  [$LABEL run $i] exit=$exit_code peak_rss=${rss}KB wall=${wall_s}s majf=$majf mem_avail_before=${mem_before}KB" >&2
  rm -f "$tmp"
done
