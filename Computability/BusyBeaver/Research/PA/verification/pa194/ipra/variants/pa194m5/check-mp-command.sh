#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

prefix=$(cd -- "${1:?checked M5 modus ponens prefix required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$prefix:$(cat "$prefix/leanpath.txt")"

theorems=(PA194ProgramCompare.comparePrefix PA194ProgramGuard.guard PA194M5MPGuard.guard
  PA194M5MPCommand.command PA194M5MPFields.resultFields)
sources=()
for theorem in "${theorems[@]}"; do
  module=${theorem%%.*}
  source="$here/$module.lean"
  log="$out/$module.log"
  sources+=("$source")
  if ! lean -j1 -M5000 -R "$here" -o "$out/$module.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  rg -Fxq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
done
sha256sum "${sources[@]}" "$here/check-mp-command.sh" "$out"/*.olean >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
