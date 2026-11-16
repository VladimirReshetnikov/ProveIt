#!/usr/bin/env bash
set -euo pipefail
repo=$(realpath "${1:?repository root required}")
out=$(realpath -m "${2:?fresh output directory required}")
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$repo"
ulimit -c 0
mkdir "$out"
sha256sum -c "$here/conditional-native-pins.sha256"
mapfile -t stages < "$here/conditional-native-stages.txt"
for stage in "${stages[@]}"; do
  [[ -d "$stage" ]] || { printf 'Missing stage: %s\n' "$stage" >&2; exit 1; }
done
stage_path=$(IFS=:; printf '%s' "${stages[*]}")
export LEAN_PATH="$out:$stage_path:$(lake env printenv LEAN_PATH)"
rebuild() {
  local src=$1 mod=$2 reports=$3
  local log="$out/$mod.log"
  if ! lean -j1 -R "$src" -M 6000 -o "$out/$mod.olean" "$src/$mod.lean" > "$log" 2>&1; then
    head -40 "$log"
    return 1
  fi
  if rg -q "sorryAx|declaration uses 'sorry'" "$log"; then
    cat "$log"
    return 1
  fi
  [[ $(rg -c 'depends on axioms:' "$log") == "$reports" ]]
}
rebuild "$here" PA194ConditionalNativeForward 3
rebuild "$here" PA194ConditionalDenseEndpoint 2
sha256sum -c "$here/conditional-native-pins.sha256"
printf 'PASS: conditional directions for the native PA194 sentence; lower dependencies staged.\n'
