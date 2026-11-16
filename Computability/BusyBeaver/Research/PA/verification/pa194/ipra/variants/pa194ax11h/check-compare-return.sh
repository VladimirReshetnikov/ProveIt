#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
providers=${1:?checked provider LEAN_PATH file required}
out=${2:?fresh output directory required}
[[ -f "$providers" ]] || { echo 'Provider LEAN_PATH file not found' >&2; exit 2; }
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
IFS=: read -ra paths <<< "$out:$(cat "$providers")"
declare -A seen=(); search=()
for path in "${paths[@]}"; do
  if [[ -n "$path" && -z ${seen[$path]+present} ]]; then seen["$path"]=1; search+=("$path"); fi
done
LEAN_PATH=$(IFS=:; printf '%s' "${search[*]}"); export LEAN_PATH
for mod in PA194AX11HSourceAt PA194AX11HCompareRows PA194AX11HCandidateDrain PA194AX11HCompare PA194AX11HCompareReturn; do
  log="$out/$mod.log"
  if ! lean -j1 -M6000 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" > "$log" 2>&1; then cat "$log"; exit 1; fi
  cat "$log"
  if rg -q "error:|error\(|sorryAx|Lean.ofReduceBool|declaration uses .sorry." "$log"; then exit 1; fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'PA194AX11HCompareReturn.compareAndReturn' depends on axioms: [propext, Classical.choice, Quot.sound]" "$out/PA194AX11HCompareReturn.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
