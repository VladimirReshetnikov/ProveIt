#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate (PA194P5, PA194TDY, or PA194C32) required}
case "$candidate" in
  PA194P5 | PA194TDY | PA194C32) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
model=$(cd -- "${2:?verified selector model stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$model/leanpath.txt")"

mod=${candidate}Native
dir="$here/${candidate,,}"
log="$out/$mod.log"
if ! lean -j1 -M5500 -R "$dir" -o "$out/$mod.olean" "$dir/$mod.lean" > "$log" 2>&1; then
  head -45 "$log"
  exit 1
fi
cat "$log"
rg -Fxq "'$mod.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf 'PASS %s\n' "$mod"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
