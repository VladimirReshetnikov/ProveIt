#!/usr/bin/env bash
set -euo pipefail
if (($# != 13)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT NATIVE_OUTPUT FETCH_OPEN_OUTPUT FETCH_OPEN_LOG PROJECT PACKAGE DISPATCH_RECEIPT NATIVE_RECEIPT FETCH_OPEN_RECEIPT NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); native=$(realpath "$5"); fetch=$(realpath "$6"); log=$(realpath "$7"); project=$(realpath "$8"); package=$(realpath "$9"); receipt=$(realpath "${10}"); native_receipt=$(realpath "${11}"); fetch_receipt=$(realpath "${12}"); out=$(realpath -m "${13}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
python3 - "$out" "$source" "$base" "$dispatch" "$native" "$fetch" "$project" "$package" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2:]):
 if out.is_relative_to(root) or root.is_relative_to(out): raise SystemExit('output/input overlap: '+str(root))
PY
rg -Fq 'PASS: source scheduler fetch/decode in all PRA models; native decoder stage and prebuilt foundations as documented.' "$log" || { echo 'Missing completed open fetch replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 c61e49afb3836f151e513209d421b7b01e5c27c0b6e76e7b82ac1ddafec2a415 "$native_receipt" \
 75bf7f0425037d6e90406c7547f5ae3cfca855f0c4551d76b39266a12728d8ac "$fetch_receipt" \
 700993d797bc92431264fce413d2ac0904c84aab94a9e603169ee5efec35241f "$source/PA194Transfer42Open.lean" \
 d18123d5db02765668fd1258b6c1460e8db508392d1ad795fd0eb11120eabe2d "$source/PA194Transfer42OpenComplete.lean" \
 55ad14f36ddbc2833205910654beb3527a1b328da613e14de1b7a49b86774db9 "$source/PA194Transfer45Open.lean" \
 c3f8e4f0ad09e51263b716cfe17e13b2aa3929b61beeb55e595a4d892524b5a5 "$source/PA194Transfer45OpenComplete.lean" \
 5eee7c569cf013b61ea275200409ca116b73cfb83bc11fdb88db590e684e0b76 "$source/PA194DispatchTransfersOpen.lean" \
 6ae06ab16bf1565e5b86a2fa06b5d0131304379db064122d6786dd3803eac0cf "$source/PA194SchedulerDispatchOpen.lean" \
 bc29383624632f1c5088240dab020428698580aebd161636b1635b175c5e4d3e "$source/PA194SchedulerBranchesOpen.lean" | sha256sum -c -
 python3 - "$dispatch" "$receipt" "$native" "$native_receipt" "$fetch" "$fetch_receipt" "$base" <<'PY'
import hashlib,json,pathlib,sys
dispatch,receipt,native,native_receipt,fetch,fetch_receipt,base=map(pathlib.Path,sys.argv[1:])
for root,rec,count in ((dispatch,receipt,26),(native,native_receipt,10),(fetch,fetch_receipt,6)):
 expected=json.loads(rec.read_text()); actual={p.name for p in root.glob('*.olean')}
 if len(actual)!=count or actual!=set(expected): raise SystemExit('object set changed: '+str(root))
 for name,h in expected.items():
  p=root/name
  if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=h: raise SystemExit('object changed: '+str(p))
entries=json.loads((base/'source-closure.json').read_text())
if len(entries)!=270: raise SystemExit('wrong base closure size')
for e in entries:
 p=pathlib.Path(e['source']); obj=base.joinpath(*e['module'].split('.')).with_suffix('.olean')
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=e['sha256'] or not obj.is_file(): raise SystemExit('base source changed/missing: '+e['module'])
print('26 dispatch, 10 native, 6 fetch objects and 270 source hashes/objects checked.')
PY
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$fetch:$native:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194Transfer42Open PA194Transfer42OpenComplete PA194Transfer45Open PA194Transfer45OpenComplete PA194DispatchTransfersOpen PA194SchedulerDispatchOpen PA194SchedulerBranchesOpen; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194Transfer42Open:runDrain PA194Transfer42OpenComplete:transferComplete PA194Transfer45Open:runDrain PA194Transfer45OpenComplete:transferComplete PA194DispatchTransfersOpen:transferToDispatch PA194SchedulerDispatchOpen:fetchDecodeDispatch PA194SchedulerBranchesOpen:fetchDecodeBranches; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: scheduler fetch/decode and pinned source dispatch branches in all PRA models; staged source outputs and prebuilt foundations as documented.'
