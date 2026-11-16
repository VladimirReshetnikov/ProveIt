#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate required}
parent=$(cd -- "${2:?checked parent row stage required}" && pwd)
selector=$(cd -- "${3:?checked primary selector stage required}" && pwd)
out=${4:?output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
test -s "$selector/PA194SELSegment.olean"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
python3 -I "$here/generate-rows.py" "$repo" "$out" "$candidate"
export LEAN_PATH="$(python3 -I - "$out" "$selector" "$parent" <<'PY'
from pathlib import Path
import sys

out, selector, parent = sys.argv[1:]
paths = [out, selector, parent]
for stage in (parent, selector):
    recorded = Path(stage) / "leanpath.txt"
    if recorded.is_file():
        paths.extend(recorded.read_text().strip().split(":"))
print(":".join(dict.fromkeys(path for path in paths if path)))
PY
)"

check() {
  local source=$1 mod=${1##*/} log
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5500 -R "$(dirname -- "$source")" -o "$out/$mod.olean" "$source" >"$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then return 1; fi
  printf 'PASS %s\n' "$mod"
}

check "$here/PA194GuardedSelectors.lean"
check "$out/PA194${candidate}SELRows.lean"
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
