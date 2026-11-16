#!/usr/bin/env bash
set -euo pipefail
if (($# != 17)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT NATIVE_OUTPUT FETCH_OPEN_OUTPUT FETCH_OPEN_LOG PROJECT PACKAGE DISPATCH_RECEIPT NATIVE_RECEIPT FETCH_OPEN_RECEIPT NEW_OUTPUT BRANCH_OUTPUT UNIFIED_OUTPUT TRANSFERS_OUTPUT COMPOSE_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); native=$(realpath "$5"); fetch=$(realpath "$6"); log=$(realpath "$7"); project=$(realpath "$8"); package=$(realpath "$9"); receipt=$(realpath "${10}"); native_receipt=$(realpath "${11}"); fetch_receipt=$(realpath "${12}"); out=$(realpath -m "${13}"); branch=$(realpath "${14}"); unified=$(realpath "${15}"); transfers=$(realpath "${16}"); compose=$(realpath "${17}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
python3 - "$out" "$source" "$base" "$dispatch" "$native" "$fetch" "$branch" "$unified" "$transfers" "$compose" "$project" "$package" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2:]):
 if out.is_relative_to(root) or root.is_relative_to(out): raise SystemExit('output/input overlap: '+str(root))
PY
rg -Fq 'PASS: source scheduler fetch/decode in all PRA models; native decoder stage and prebuilt foundations as documented.' "$log" || { echo 'Missing completed open fetch replay' >&2; exit 1; }
rg -Fq 'PASS: fresh and positive source-fetch branch equalities in native iPRA; staged source outputs and prebuilt foundations as documented.' /tmp/pa194-fetch-native-replay.log || { echo 'Missing completed branch replay' >&2; exit 1; }
rg -Fq 'PASS: unified source-fetch equality in native iPRA; staged source outputs and prebuilt foundations as documented.' /tmp/pa194-unified-fetch-native-staged-replay.log || { echo 'Missing completed unified replay' >&2; exit 1; }
rg -Fq 'PASS: scheduler fetch/decode and pinned source dispatch branches in all PRA models; staged source outputs and prebuilt foundations as documented.' /tmp/pa194-scheduler-branches-open-replay.log || { echo 'Missing completed transfers replay' >&2; exit 1; }
rg -Fq 'PASS: composed source fetch/decode equality in native iPRA; staged source outputs and prebuilt foundations as documented.' /tmp/pa194-fetch-decode-native-replay.log || { echo 'Missing composed native replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 c61e49afb3836f151e513209d421b7b01e5c27c0b6e76e7b82ac1ddafec2a415 "$native_receipt" \
 75bf7f0425037d6e90406c7547f5ae3cfca855f0c4551d76b39266a12728d8ac "$fetch_receipt" \
 9158133e05a7729b86124d64caf0c7270e83f66ab8790ad9a20a07424eb9e353 "$source/PA194FreshFetchNative.lean" \
 e413ec8c90af5f20e6e4f7cba89621758e3bcef2084f8026e99d7a184a5bfe9b "$source/PA194PositiveFetchNative.lean" \
 b303caabe37985351be98a20a6a569bd7ddd2030692c2541b18b0a5fa5c91fb6 "$source/PA194UnifiedFetchNative.lean" \
 055b7fd82f25359bb41ad3045fab9f3f2e87e3b9dd0d12576d7415dea7302599 "$branch/PA194FreshFetchNative.olean" \
 dc01e44dc8f0ba3e1ba053dad70c397efc33e2b2de7888fc4227d6b608cdf75e "$branch/PA194PositiveFetchNative.olean" \
 494436ed20be909d4d6986066ff9ae7d5afcc0d771d98d2104ad806b94cda996 "$unified/PA194UnifiedFetchNative.olean" \
 e76e4fedcef9c71451fc8e055c0938e73ff77c7014e49b5312c748682cbee90a "$source/PA194FetchDecodeNative.lean" \
 56a976f87fbf74c6fa980ba727b704e45b81f466926d7fb71b6300dfc7ee1a37 "$transfers/PA194DispatchTransfersOpen.olean" \
 b14127cb84a94fd46b2182150da1df9d4ac7b5a7a68371d499559a0f09c6d948 "$transfers/PA194SchedulerBranchesOpen.olean" \
 becf8de58bffca620f200e47f597af4469c7f1f1c848cbd28d52f70cfed91f9f "$transfers/PA194SchedulerDispatchOpen.olean" \
 e80d83a4a7aafce2e50fce7cb40ae0af8770b174060de0d850074f35d8c9c5e6 "$transfers/PA194Transfer42Open.olean" \
 772be3d4af07ff1c905ef90dceca222440ac1bdf890deb3661d09dff6f96cb1b "$transfers/PA194Transfer42OpenComplete.olean" \
 bbc7f8eb2f962a5fe84cd022b5d5a530b4d277a1aae55c704fab677b0b019cd6 "$transfers/PA194Transfer45Open.olean" \
 e8ced8ac19df49179361e189182a16e4ae7f15a7f6effc9d56367f594f056890 "$transfers/PA194Transfer45OpenComplete.olean" \
 ea0aa0ed1dc8ebd8d75d9436315ac5b2850ee988beb5916b44027241635f9200 "$compose/PA194FetchDecodeNative.olean" \
 75c5b785b3c781ca3f41b055894fa7ad9c598a62831fda0fcf74878ede324c95 "$source/PA194DispatchTransfersNative.lean" | sha256sum -c -
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
export LEAN_PATH="$out:$compose:$transfers:$unified:$branch:$fetch:$native:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194DispatchTransfersNative; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
for spec in PA194DispatchTransfersNative:modelSentence PA194DispatchTransfersNative:classicalPRA PA194DispatchTransfersNative:nativeIPRA; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: source dispatch transfer equality in native iPRA; staged source outputs and prebuilt foundations as documented.'
