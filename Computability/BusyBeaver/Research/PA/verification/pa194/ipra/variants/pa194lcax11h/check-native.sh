#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

literal=$(cd -- "${1:?checked LC_AX11H literal stage required}" && pwd)
ax11h=$(cd -- "${2:?checked AX11H final stage required}" && pwd)
bridge=$(cd -- "${3:?checked shared bounded transfer stage required}" && pwd)
out=${4:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$bridge" "$literal" "$ax11h" <<'PY'
from pathlib import Path
import sys

out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / 'leanpath.txt').read_text().strip().split(':'))
print(':'.join(dict.fromkeys(p for p in paths if p)))
PY
)"
for theorem in PA194LCAX11HRelativeNative.relative_nonhalt \
    PA194LCAX11HConditionalFinal.consistency_iff_literal_nonhalt; do
  module=${theorem%%.*}
  log="$out/$module.log"
  if ! lean -j1 -M5500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  tr -s '[:space:]' ' ' <"$log" |
    rg -Fq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]"
done
printf '%s\n' "$LEAN_PATH" >"$out/leanpath.txt"
