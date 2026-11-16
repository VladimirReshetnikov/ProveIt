#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
controller=$(cd -- "${1:?checked LC_C controller stage required}" && pwd)
coverage=$(cd -- "${2:?checked LC_C coverage stage required}" && pwd)
out=${3:?fresh output directory required}
[[ ! -e "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -f "$controller/PA194LCCNative.olean"
test -f "$controller/leanpath.txt"
test -f "$coverage/PA194LCCCoverage.olean"
test -f "$coverage/leanpath.txt"
mkdir -p "$out"; out=$(cd -- "$out" && pwd)
cd "$repo"
IFS=: read -ra providers <<< "$out:$controller:$coverage:$(cat "$controller/leanpath.txt"):$(cat "$coverage/leanpath.txt")"
declare -A seen=()
search=()
for provider in "${providers[@]}"; do
  if [[ -n "$provider" && -z ${seen[$provider]+present} ]]; then
    seen["$provider"]=1
    search+=("$provider")
  fi
done
LEAN_PATH=$(IFS=:; printf '%s' "${search[*]}")
export LEAN_PATH
log="$out/PA194LCCFinal.log"
if ! lean -j1 -M5500 -R "$here" -o "$out/PA194LCCFinal.olean" "$here/PA194LCCFinal.lean" > "$log" 2>&1; then cat "$log"; exit 1; fi
cat "$log"
if rg -q "error:|error\(|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
rg -Fxq "'PA194LCCFinal.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
echo 'PASS PA194LCCFinal'
