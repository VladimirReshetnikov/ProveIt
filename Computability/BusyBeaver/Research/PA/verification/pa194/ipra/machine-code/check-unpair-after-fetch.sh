#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then
  echo "usage: $0 REPO SOURCE_DIR PASSED_FETCH_OUTPUT PASSED_FETCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT" >&2
  exit 2
fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); log=$(realpath "$4")
project=$(realpath "$5"); package=$(realpath "$6"); out="$7"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" ]] || { echo "Output must not already exist: $out" >&2; exit 2; }
rg -Fq "PA194SchedulerFetchModel: checked (270 standalone modules, 270 compiled now, objects in $base)" "$log" || { echo 'Fetch baseline lacks a completed full-build report' >&2; exit 1; }
[[ -f "$base/source-closure.json" && -f "$base/PA194SchedulerFetchModel.olean" && -L "$base/foundation-view/DiophantineConsistency" ]] || exit 1
printf '%s  %s\n' \
 eed485c540d767b9b7c15ebced5acf69979123da0615cdeda5b84c66e3a2a287 "$source/PA194UnpairRound.lean" \
 3e0346ad8d9aa98496019a2c49eb2ff4a1f3f5e3f33d3dde2e903c8257cc10a6 "$source/PA194UnpairDrainLoop.lean" \
 6a954420710f3e2b86cccf4e5bf8baf8c81e185ee9008a988f52211a285e6922 "$source/PA194UnpairDrainInvariant.lean" \
 2592b6c824e4c607ee95918026f33ce51efa87052cb032c0a16aedf7928c46d9 "$source/PA194UnpairDrainModel.lean" \
 4cf3b0163e3ac9e7ddbc4be4df274b9c03a34051894dbf476810bbee0c737607 "$source/PA194UnpairDrainComplete.lean" | sha256sum -c -
python3 - "$base" "$project" <<'PY'
import hashlib,json,pathlib,sys
base,project=map(pathlib.Path,sys.argv[1:])
items=json.loads((base/'source-closure.json').read_text())
if len(items)!=270: sys.exit('wrong closure size')
for ent in items:
 p=pathlib.Path(ent['source']); obj=base.joinpath(*ent['module'].split('.')).with_suffix('.olean')
 # with_suffix is correct for both flat and dotted module paths
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=ent['sha256'] or not obj.is_file():
  sys.exit('missing or changed baseline source/object: '+ent['module'])
graph=(base/'foundation-view/DiophantineConsistency').resolve()
pins={'PRAHistoryResultGraph':'2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae','PRAHistoryTrace':'4b3ea00b4fbf5790008bddc61a69d2b7bdf84551e67084219014b57bd6402db2','PRAHistoryIterator':'b359da5684d709684b25fcd7c7073804a91044fc54ae0f2bfc9b44a7b1844583','PRAHistorySingletonSequence':'e976a9cc5de9e9ca257f78e16ea444a32684ecc3cb74f4c8f0bef7fabbb1ce40','PRAHistorySingletonMembership':'85aeb8494921b2211b7c4ca01b0fce4b5153ce0839ad6bc5e087dfdbb047c45d','PRAHistoryLengthUnique':'d225bca0cd681778109ef906169e7f7a0549289635c81e2a987f3cd67aab1c58'}
real=[]
for p in graph.glob('*.olean'):
 if p.is_symlink():
  if not p.resolve().is_relative_to(project/'DiophantineConsistency'): sys.exit('graph symlink outside project foundation: '+str(p))
 else: real.append(p.stem)
if set(real)!=set(pins): sys.exit('graph namespace real-object list differs')
for name,h in pins.items():
 if hashlib.sha256((graph/(name+'.olean')).read_bytes()).hexdigest()!=h: sys.exit('graph hash mismatch: '+name)
print('Baseline source hashes, object presence and graph fallback pins checked.')
PY
mkdir -p "$out"
out=$(realpath "$out")
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194UnpairRound PA194UnpairDrainLoop PA194UnpairDrainInvariant PA194UnpairDrainModel PA194UnpairDrainComplete; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
  if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
  rg 'depends on axioms:' "$out/$m.log"
done
rg -Fq "'PA194UnpairDrainComplete.zeroXRound' depends on axioms:" "$out/PA194UnpairDrainComplete.log"
sha256sum "$source"/PA194Unpair{Round,DrainLoop,DrainInvariant,DrainModel,DrainComplete}.lean
printf 'PASS: site-34 positive and zero-X decoder rounds, with IΣ₁ for model-length zero-X drain; graph and general foundations remain prebuilt.\n'
