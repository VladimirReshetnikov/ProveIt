#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

model=$(cd -- "${1:?checked radix model stage required}" && pwd)
split=$(cd -- "${2:?checked primitive-recursive radix split stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
test -f "$model/PA194RadixModel.olean"
test -f "$split/PA194RadixSplit.olean"
test ! -e "$out"
mkdir -p "$out"
out=$(cd -- "$out" && pwd)

export LEAN_PATH="$(python3 -I - "$out" "$split" "$model" <<'PY'
from pathlib import Path
import sys
out, *stages = sys.argv[1:]
paths = [out, *stages]
for stage in stages:
    paths.extend((Path(stage) / "leanpath.txt").read_text().strip().split(":"))
print(":".join(dict.fromkeys(path for path in paths if path)))
PY
)"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"

check() {
  local module=$1
  shift
  local log="$out/$module.log"
  if ! lean -j1 -M4500 -R "$here" -o "$out/$module.olean" "$here/$module.lean" >"$log" 2>&1; then
    cat "$log"
    exit 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then exit 1; fi
  for theorem in "$@"; do
    rg -Fxq "'PA194RadixRecoding.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$log"
  done
  printf 'PASS %s\n' "$module"
}
check PA194RadixRecoding historySucc lookupOlder
check PA194RadixRecodingEquation stepValueModel recodeSucc
check PA194RadixRecodingRoundTrip recodeConstructor recodeDigit roundTrip injective radixFiveRoundTrip

sha256sum "$here"/PA194RadixRecoding{,Equation,RoundTrip}.lean "$here/check-radix-recoding.sh" \
  "$out"/*.olean >"$out/sha256.txt"
