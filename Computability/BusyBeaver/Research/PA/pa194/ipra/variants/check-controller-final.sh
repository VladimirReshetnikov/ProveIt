#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate (PA194AD, PA194HX, or PA194LC) required}
case "$candidate" in
  PA194AD | PA194HX | PA194LC) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
controller=$(cd -- "${2:?verified controller stage required}" && pwd)
coverage=$(cd -- "${3:?verified source coverage stage required}" && pwd)
out=${4:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
IFS=: read -ra providers <<< "$out:$(cat "$coverage/leanpath.txt"):$(cat "$controller/leanpath.txt")"
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

mod=${candidate}Final
dir="$here/${candidate,,}"
log="$out/$mod.log"
if ! lean -j1 -M5500 -R "$dir" -o "$out/$mod.olean" "$dir/$mod.lean" > "$log" 2>&1; then
  head -45 "$log"
  exit 1
fi
cat "$log"
rg -Fxq "'$mod.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf 'PASS %s\n' "$mod"
