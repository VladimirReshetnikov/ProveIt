#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?verified primary literal stage required}" && pwd)
shared=$(cd -- "${2:?verified PA194B stage required}" && pwd)
execution=$(cd -- "${3:?verified machine execution stage required}" && pwd)
or_base=$(cd -- "${4:?verified PA194OR register-file stage required}" && pwd)
out=${5:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"

export LEAN_PATH="$out:$or_base:$execution:$shared:$(cat "$literal/leanpath.txt")"
for mod in PA194RegisterDecrement PA194SpareSweep PA194RegisterIncrement PA194RegisterMark PA194RegisterBoxes; do
  log="$out/$mod.log"
  if ! lean -j1 -M5300 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" > "$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
