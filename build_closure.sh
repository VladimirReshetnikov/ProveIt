#!/bin/sh
LOG=build_closure.log
: > "$LOG"
while IFS= read -r m; do
  m=$(printf '%s' "$m" | tr -d '\r')
  [ -z "$m" ] && continue
  echo "=== BUILD $m ===" >> "$LOG"
  start=$(date +%s)
  if LAKE_JOBS=1 lake build "+$m" >> "$LOG" 2>&1; then
    end=$(date +%s)
    echo "=== OK $m ($((end-start))s) ===" >> "$LOG"
  else
    echo "=== FAIL $m ===" >> "$LOG"
    exit 1
  fi
done < order.txt
echo "=== ALL DONE ===" >> "$LOG"
