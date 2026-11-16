#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

out=${1:?output directory required}
stages=${2:-/dev/shm/pa194-literal-scheduler-correctness/leanpath.txt}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
machine="$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$out:$(cat "$stages")"

python3 -I "$here/bind_tables.py" "$repo" "$out"

check() {
  local source=$1
  local mod=${source##*/}
  mod=${mod%.lean}
  local log="$out/$mod.log"
  if ! lean -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

check "$out/PA194Rows.lean"
check "$machine/PA194RegisterPermutation.lean"
for module in Table Ordinary Step Bounded Store File Frame; do
  check "$here/PA194AD$module.lean"
done
