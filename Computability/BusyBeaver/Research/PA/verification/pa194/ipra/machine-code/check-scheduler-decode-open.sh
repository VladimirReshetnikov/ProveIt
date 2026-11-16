#!/usr/bin/env bash
set -euo pipefail
if (($# != 11)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT NATIVE_OUTPUT NATIVE_LOG PROJECT PACKAGE DISPATCH_RECEIPT NATIVE_RECEIPT NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); native=$(realpath "$5"); log=$(realpath "$6"); project=$(realpath "$7"); package=$(realpath "$8"); receipt=$(realpath "$9"); native_receipt=$(realpath "${10}"); out=$(realpath -m "${11}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
python3 - "$out" "$source" "$base" "$dispatch" "$native" "$project" "$package" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2:]):
 if out.is_relative_to(root) or root.is_relative_to(out): raise SystemExit('output/input overlap: '+str(root))
PY
rg -Fq 'PASS: universally closed native iPRA site-34 to site-42 decoder equality; machine/dispatch source outputs and prebuilt foundations as documented.' "$log" || { echo 'Missing completed native decoder replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 c61e49afb3836f151e513209d421b7b01e5c27c0b6e76e7b82ac1ddafec2a415 "$native_receipt" \
 2cdc0afad253ebd8cdeb0623fc7df426f976118994e9fe45c49772c71dc1651e "$source/PA194SourceDrainOpen.lean" \
 fc0443b0b08a7ea4ebb4880903f0765784ae154ef57a2a5fc8ea2c5c130474e3 "$source/PA194SourceRestoreOpen.lean" \
 5185e58b51a56a032d6df238c13d82e2296f136f3794c2e32fd07d6c4dea823f "$source/PA194SourceFetchOpen.lean" \
 7b8d2dddd010c590b3e0ed973820a5b9d8b83a424fdeb00efb179e7fc6fbcad6 "$source/PA194SchedulerFieldsOpen.lean" \
 7277546681e51efc1a3eb0e2c11afae0483c4c1eaaa1e1b8091ab3f7a31186ef "$source/PA194SchedulerFetchOpen.lean" \
 94e32307e9917716f1cd9f8449fb38b6287de8c0008adbf88cbab0e3b6e9279a "$source/PA194SchedulerDecodeOpen.lean" | sha256sum -c -
 python3 - "$dispatch" "$receipt" "$native" "$native_receipt" "$base" <<'PY'
import hashlib,json,pathlib,sys
dispatch,receipt,native,native_receipt,base=map(pathlib.Path,sys.argv[1:])
for root,rec,count in ((dispatch,receipt,26),(native,native_receipt,10)):
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
print('26 dispatch objects, 10 native-decoder objects and 270 source hashes/objects checked.')
PY
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$native:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194SourceDrainOpen PA194SourceRestoreOpen PA194SourceFetchOpen PA194SchedulerFieldsOpen PA194SchedulerFetchOpen PA194SchedulerDecodeOpen; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194SourceDrainOpen:runDrain PA194SourceRestoreOpen:runRestore PA194SourceFetchOpen:freshSourceFetch PA194SchedulerFieldsOpen:packedNextN PA194SchedulerFieldsOpen:freshFields PA194SchedulerFetchOpen:fetchPrefix PA194SchedulerDecodeOpen:fetchAndDecode; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: source scheduler fetch/decode in all PRA models; native decoder stage and prebuilt foundations as documented.'
