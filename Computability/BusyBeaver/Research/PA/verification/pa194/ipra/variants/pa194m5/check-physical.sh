#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

source_stage=$(cd -- "${1:?checked M5 source stage required}" && pwd)
base=$(cd -- "${2:?checked PA1944L physical model stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$(python3 - "$out" "$source_stage" "$base" <<'PY'
from pathlib import Path
import sys

out, *stages = map(Path, sys.argv[1:])
paths = [str(p) for p in (out, *stages)]
for stage in stages:
    paths.extend((stage / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"

check() {
  local file=$1 mod=${1##*/} log
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$(dirname -- "$file")" -o "$out/$mod.olean" "$file" >"$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error[:(]|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}

python3 -I "$here/../generate-source-table.py" PA194M5 "$repo" "$out"
python3 -I "$here/../generate-indexed-startup.py" PA194M5 "$repo" "$out"
for mod in PA194SourceContracts PA194TrieRoot PA194VariantController PA194TrieSourceController; do
  check "$here/../$mod.lean"
done
check "$out/PA194M5Data.lean"
for suffix in Rows BoxAgreement Checks Numerical; do
  check "$here/PA194M5$suffix.lean"
done
for file in "$out"/PA194M5StartupChunk*.lean "$out/PA194M5StartupComplete.lean"; do
  check "$file"
done
for suffix in ModelStartup Initializer Controller; do
  check "$here/PA194M5$suffix.lean"
done
rg -Fxq "'PA194M5Controller.halt_iff_site10' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194M5Controller.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
