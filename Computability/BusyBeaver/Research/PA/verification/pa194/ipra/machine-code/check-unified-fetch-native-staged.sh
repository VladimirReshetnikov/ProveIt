#!/usr/bin/env bash
set -euo pipefail
if (($# != 14)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT NATIVE_OUTPUT FETCH_OPEN_OUTPUT FETCH_OPEN_LOG PROJECT PACKAGE DISPATCH_RECEIPT NATIVE_RECEIPT FETCH_OPEN_RECEIPT NEW_OUTPUT BRANCH_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); native=$(realpath "$5"); fetch=$(realpath "$6"); log=$(realpath "$7"); project=$(realpath "$8"); package=$(realpath "$9"); receipt=$(realpath "${10}"); native_receipt=$(realpath "${11}"); fetch_receipt=$(realpath "${12}"); out=$(realpath -m "${13}"); branch=$(realpath "${14}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
python3 - "$out" "$source" "$base" "$dispatch" "$native" "$fetch" "$branch" "$project" "$package" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2:]):
 if out.is_relative_to(root) or root.is_relative_to(out): raise SystemExit('output/input overlap: '+str(root))
PY
rg -Fq 'PASS: source scheduler fetch/decode in all PRA models; native decoder stage and prebuilt foundations as documented.' "$log" || { echo 'Missing completed open fetch replay' >&2; exit 1; }
rg -Fq 'PASS: fresh and positive source-fetch branch equalities in native iPRA; staged source outputs and prebuilt foundations as documented.' /tmp/pa194-fetch-native-replay.log || { echo 'Missing completed branch replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 c61e49afb3836f151e513209d421b7b01e5c27c0b6e76e7b82ac1ddafec2a415 "$native_receipt" \
 75bf7f0425037d6e90406c7547f5ae3cfca855f0c4551d76b39266a12728d8ac "$fetch_receipt" \
 9158133e05a7729b86124d64caf0c7270e83f66ab8790ad9a20a07424eb9e353 "$source/PA194FreshFetchNative.lean" \
 e413ec8c90af5f20e6e4f7cba89621758e3bcef2084f8026e99d7a184a5bfe9b "$source/PA194PositiveFetchNative.lean" \
 b303caabe37985351be98a20a6a569bd7ddd2030692c2541b18b0a5fa5c91fb6 "$source/PA194UnifiedFetchNative.lean" \
 055b7fd82f25359bb41ad3045fab9f3f2e87e3b9dd0d12576d7415dea7302599 "$branch/PA194FreshFetchNative.olean" \
 dc01e44dc8f0ba3e1ba053dad70c397efc33e2b2de7888fc4227d6b608cdf75e "$branch/PA194PositiveFetchNative.olean" | sha256sum -c -
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
export LEAN_PATH="$out:$branch:$fetch:$native:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194UnifiedFetchNative; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194UnifiedFetchNative:modelSentence PA194UnifiedFetchNative:classicalPRA PA194UnifiedFetchNative:nativeIPRA; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: unified source-fetch equality in native iPRA; staged source outputs and prebuilt foundations as documented.'
