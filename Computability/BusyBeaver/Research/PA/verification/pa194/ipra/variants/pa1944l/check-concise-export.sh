#!/usr/bin/env bash
set -euo pipefail

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
native=${1:?checked PA1944L final stage required}
out=${2:?fresh output directory required}
table="$here/../../../../../docs/pa1944l_research_2026-11-14/machine/machine.tm"
table_hash=c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253
printf '%s  %s\n' "$table_hash" "$table" | sha256sum -c -

bash "$here/../../native-endpoint/check-concise-export.sh" \
  "$repo" "$native" "$out" PA1944LFinal "$here/PA1944LConcise.lean"

IFS=: read -ra providers <"$out/leanpath.txt"
for provider in "${providers[@]}"; do
  if [[ -f "$provider/PA1944LData.olean" ]]; then
    sha256sum "$provider/PA1944LData.olean" >>"$out/sha256.txt"
    break
  fi
done
printf '%s  %s\n' "$table_hash" "$table" >>"$out/sha256.txt"
