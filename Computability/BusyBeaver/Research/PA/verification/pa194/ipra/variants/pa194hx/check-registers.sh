#!/usr/bin/env bash
set -euo pipefail
ulimit -s unlimited
ulimit -c 0

register=$(cd -- "${1:?verified shared register stage required}" && pwd)
startup=$(cd -- "${2:?verified PA194HX startup stage required}" && pwd)
out=${3:?fresh output directory required}
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
mkdir -p "$out"
out=$(cd -- "$out" && pwd)
cd "$repo"
export LEAN_PATH="$out:$startup:$(cat "$register/leanpath.txt")"

labels=Computability/BusyBeaver/Research/PA/docs/pa194_research_2026-11-14/hx194/machine/pa194hx.labels.json
printf '%s  %s\n' 3188b59b6479f9664074bb5371bcf2c5c0943f529be1496df35f5cbd2cb77d6c "$labels" | sha256sum -c
python3 -I - "$labels" "$here/PA194HXNativeLabels.lean" <<'PY'
import json
from pathlib import Path
import re
import sys

expected = json.loads(Path(sys.argv[1]).read_text())
source = Path(sys.argv[2]).read_text()
declared = re.search(r"def labels : List Nat := (\[[^\n]*\])", source)
if declared is None or json.loads(declared.group(1)) != expected:
    raise SystemExit("Lean native labels differ from the pinned HX packet")
PY

check() {
  local mod=$1
  local log="$out/$mod.log"
  if ! lean -j1 -M5600 -R "$here" -o "$out/$mod.olean" "$here/$mod.lean" > "$log" 2>&1; then
    cat "$log"
    return 1
  fi
  cat "$log"
  if rg -q "error:|sorryAx|Lean.ofReduceBool|declaration uses 'sorry'" "$log"; then
    return 1
  fi
  printf 'PASS %s\n' "$mod"
}

for mod in Contracts NativeLabels NativeAlignment ContractSound RowData RowAgreement PhysicalConditional \
    GenericMark MarkOracle DecrementRows IncrementRows BoxAgreement RootEncoding SourceRoot SourceArgs; do
  check "PA194HX$mod"
done
rg -Fxq "'PA194HXBoxAgreement.concreteBoxAgreement' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$out/PA194HXBoxAgreement.log"
printf '%s\n' "$LEAN_PATH" > "$out/leanpath.txt"
