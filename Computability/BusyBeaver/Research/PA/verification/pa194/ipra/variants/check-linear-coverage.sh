#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

candidate=${1:?candidate required}
case "$candidate" in
  PA194LC | PA1944L | PA194LCA | PA194M4R | PA194LCB | PA194AX11H | PA194LCAX11H | PA194M5) ;;
  *) printf 'Unknown candidate %s\n' "$candidate" >&2; exit 2 ;;
esac
base=$(cd -- "${2:?verified table stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$(cat "$base/leanpath.txt")"

python3 -I "$here/generate-linear-coverage.py" "$candidate" "$out"
for source in "$out"/"${candidate}Coverage"[0-9][0-9].lean "$out/${candidate}Coverage.lean"; do
  mod=${source##*/}
  mod=${mod%.lean}
  log="$out/$mod.log"
  if ! lean -j1 -M5350 -R "$out" -o "$out/$mod.olean" "$source" > "$log" 2>&1; then
    head -45 "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    exit 1
  fi
  printf 'PASS %s\n' "$mod"
done
rg -Fxq "'${candidate}Coverage.checked' depends on axioms: [propext, Quot.sound]" "$out/${candidate}Coverage.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
