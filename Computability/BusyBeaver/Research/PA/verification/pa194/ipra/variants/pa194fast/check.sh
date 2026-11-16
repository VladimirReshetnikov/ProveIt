#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked primary literal output directory required}" && pwd)
branch=$(cd -- "${2:?checked PA194B output directory required}" && pwd)
out=${3:?fresh output directory required}
select=${4:-}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

test -f "$literal/PA194NativeLiteralFinal.olean"
test -f "$branch/PA194VariantNative.olean"
modules=(PA194Fast)
flags=()
provider="$branch"
if [[ -n "$select" ]]; then
  select=$(cd -- "$select" && pwd)
  test -f "$branch/PA194BHalting.olean"
  test -f "$select/PA194SELHalting.olean"
  provider="$select:$provider"
  modules+=(PA194BFast PA194SELFast)
  flags+=(--companions)
fi
export LEAN_PATH="$out:$provider:$literal:$(cat "$literal/leanpath.txt")"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
python3 -I "$here/generate-rows.py" "$repo" "$out" "${flags[@]}"

check() {
  local source=$1
  local module=${source##*/}
  module=${module%.lean}
  local log="$out/$module.log"
  if ! lean -j1 -M5500 -R "$(dirname -- "$source")" -o "$out/$module.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$module"
}

check "$here/PA194GuardedShortcuts.lean"
for candidate in "${modules[@]}"; do
  check "$out/${candidate}Rows.lean"
done
for candidate in "${modules[@]}"; do
  check "$here/${candidate}Native.lean"
  rg -Fxq "'${candidate}Native.consistency_iff_literal_nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/${candidate}Native.log"
done
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
