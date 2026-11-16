#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

model=$(cd -- "${1:?checked LC_B model stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$model/leanpath.txt")"
mod=PA194LCBNative
log="$out/$mod.log"
lean -j1 -M5350 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" 2>&1 | tee "$log"
rg -Fxq "'$mod.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
