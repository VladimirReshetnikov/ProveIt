#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
out=${1:?output directory required}
source=${2:?checked AX11H source stage required}
base=${3:?checked physical model stage required}
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
export LEAN_PATH="$(python3 - "$out" "$source" "$base" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage)/'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(path for path in paths if path)))
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
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}
python3 -I "$here/../generate-source-table.py" PA194AX11H "$repo" "$out"
python3 -I "$here/../generate-indexed-startup.py" PA194AX11H "$repo" "$out"
check "$out/PA194AX11HData.lean"
for mod in Rows BoxAgreement Checks Numerical; do check "$here/PA194AX11H$mod.lean"; done
for file in "$out"/PA194AX11HStartupChunk*.lean "$out/PA194AX11HStartupComplete.lean"; do check "$file"; done
check "$here/PA194AX11HModelStartup.lean"
check "$here/PA194AX11HInitializer.lean"
rg -Fxq "'PA194AX11HInitializer.startup_root' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194AX11HInitializer.log"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
