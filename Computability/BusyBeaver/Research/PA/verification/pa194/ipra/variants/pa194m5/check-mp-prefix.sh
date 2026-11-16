#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

constructors=$(cd -- "${1:?checked M5 constructor-site stage required}" && pwd)
out=${2:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$constructors:$(cat "$constructors/leanpath.txt")"

theorems=(PA194ProgramReader.reader PA194ProgramPush.push PA194ProgramCopy.copy
  PA194M5MPField.field PA194M5MPConstructor.build PA194M5MPPush.entry PA194M5MPCopy.entry
  PA194M5MPPrefix.throughConstructor)
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
sha256sum "${sources[@]}" "$here/check-mp-prefix.sh" "$out"/*.olean >"$out/sha256.txt"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
