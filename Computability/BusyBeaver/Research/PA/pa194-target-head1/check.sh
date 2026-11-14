#!/usr/bin/env bash
set -euo pipefail
: "${IPRA_FOUNDATION_OVERLAY:?Set IPRA_FOUNDATION_OVERLAY to the matching audited Lean 4.32 Foundation object directory}"
: "${IPRA_LEAN_OVERLAY:?Set IPRA_LEAN_OVERLAY to the matching audited project object directory}"
base=Computability/BusyBeaver/Research/PA
root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-target-head1.XXXXXXXX")
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/inversion" "$root/compiler" "$root/final"
export PA194_TARGET_INVERSION_ROOT="$root/inversion" PA194_TARGET_COMPILER_ROOT="$root/compiler"
python3 - "$base/pa194-source-all-inversion/check.sh" "$root/inversion-prerequisites.sh" "$base/pa194-derivation-compiler/check.sh" "$root/compiler-prerequisites.sh" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
old='root=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-all-inversion.XXXXXXXX")'
trap='trap \'rm -rf "$root"\' EXIT'
if s.count(old) != 1 or s.count(trap) != 1:
    raise SystemExit('unexpected inversion prerequisite wrapper')
s=s.replace(old,'root=$PA194_TARGET_INVERSION_ROOT',1).replace(trap,'',1)
Path(sys.argv[2]).write_text(s)
s=Path(sys.argv[3]).read_text()
s,n=re.subn(r'^task_dir=\$\(mktemp[^\n]*\)\s*$', 'task_dir=$PA194_TARGET_COMPILER_ROOT',s,count=1,flags=re.M)
trap='trap \'rm -rf "$task_dir"\' EXIT'
old='lean -M6000 -j1 "$package/PA194DerivationCompiler.lean" | tee'
new='lean -M6000 -j1 -o "$task_dir/PA194DerivationCompiler.olean" "$package/PA194DerivationCompiler.lean" | tee'
if n != 1 or s.count(trap) != 1 or s.count(old) != 1:
    raise SystemExit('unexpected compiler prerequisite wrapper')
s=s.replace(trap,'',1).replace(old,new,1)
Path(sys.argv[4]).write_text(s)
PY
bash -n "$root/inversion-prerequisites.sh"
bash -n "$root/compiler-prerequisites.sh"
bash "$root/inversion-prerequisites.sh"
bash "$root/compiler-prerequisites.sh"
inversion="$root/inversion"
graph="$inversion/graph"
fields="$graph/fields"
choice="$fields/choice"
parent="$choice/parent"
setroot="$parent/parent"
search="$setroot/search"
source="$search/dependency"
export LEAN_PATH="$root/final:$inversion/final:$graph/final:$fields/final:$choice/final:$parent/final:$setroot/final:$search/final:$source/final:$source/update:$source/source/final:$source/source/prereq/final:$source/source/prereq/model:$source/source/prereq/source:$root/compiler:$IPRA_LEAN_OVERLAY:$IPRA_FOUNDATION_OVERLAY:$(lake env printenv LEAN_PATH)"
lean -M6000 -j1 -o "$root/final/PA194TargetCantor.olean" "$base/pa194-target-head1/PA194TargetCantor.lean" | tee "$root/final/axioms.log"
if rg -q 'sorryAx' "$root/final/axioms.log"; then
  echo 'Unexpected sorryAx in target head-1 certificate' >&2
  exit 1
fi
