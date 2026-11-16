#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

source_stage=$(cd -- "${1:?checked M6 source stage required}" && pwd)
startup=$(cd -- "${2:?checked common startup stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 -I - "$out" "$source_stage" "$startup" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
python3 -I "$here/../generate-source-table.py" PA194M6 "$repo" "$out"

check() {
  local file=$1 module=${1##*/} log
  module=${module%.lean}
  log="$out/$module.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$file")" -o "$out/$module.olean" "$file" >"$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$module"
}

for module in PA194SourceContracts PA194TrieRoot PA194VariantController PA194TrieSourceController; do
  check "$here/../$module.lean"
done
check "$out/PA194M6Data.lean"
for suffix in Rows BoxAgreement Checks Numerical Startup ModelStartup Initializer Controller; do
  check "$here/PA194M6$suffix.lean"
done
for theorem in Initializer.startup_root Controller.halt_iff_site10; do
  rg -Fxq "'PA194M6$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$out/PA194M6${theorem%%.*}.log"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
