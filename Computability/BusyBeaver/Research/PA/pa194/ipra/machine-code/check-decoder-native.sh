#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo 'usage: REPO SOURCE FETCH_OUTPUT DISPATCH_OUTPUT DISPATCH_LOG PROJECT_FOUNDATION PACKAGE_FOUNDATION DISPATCH_RECEIPT NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); source=$(realpath "$2"); base=$(realpath "$3"); dispatch=$(realpath "$4"); log=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); receipt=$(realpath "$8"); out=$(realpath -m "$9")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output must be fresh' >&2; exit 2; }
python3 - "$out" "$source" "$base" "$dispatch" "$project" "$package" <<'PY'
from pathlib import Path
import sys
out=Path(sys.argv[1]); roots=map(Path,sys.argv[2:])
for p in roots:
 if out.is_relative_to(p) or p.is_relative_to(out): raise SystemExit('output/input overlap: '+str(p))
PY
rg -Fq 'PASS: model-length source dispatch transfers and pinned tag branches; graph and general foundations remain prebuilt.' "$log" || { echo 'Missing completed dispatch source replay' >&2; exit 1; }
check_inputs() {
 printf '%s  %s\n' \
 e3b17c6b00287bfa4aeded197f4ce8772fe4da80ac110b13e1256744e66dae93 "$receipt" \
 bf15ba18f9827cb1aeb362c78a430ce71385de26bc71e89f7afd793b53824816 "$source/PA194IterateAddOpen.lean" \
 6d34b91b8a515630aaf60a605251473152f09d5363313d2145f4d6aefd6a5b8f "$source/PA194UnpairDrainOpen.lean" \
 2eeb38f7ede12a0e4e6d5ea2e6a9833f7d243ad49810b8b65f05e0df2ce2c748 "$source/PA194UnpairDrainOpenComplete.lean" \
 8b6f00c1632d4adb0dc97c59fec1d75d2d9c19123136a7aba8e0365d47c529c0 "$source/PA194DecoderRoundOpen.lean" \
 552a0d62090596a8a7e2bce4f56b38f60cfadb54b94b2a262135926901a6de9a "$source/PA194SourceReconstruct.lean" \
 d5f3876648f1d9b505c30e8c68c2e3e02c48086971f49a2e92df210531360921 "$source/PA194DecoderSynchronizationOpen.lean" \
 38b8f0fd1a58631db9908d1e60c5ffe0885a3c6dffa176355906a5a55ce8be25 "$source/PA194DecoderClockOpen.lean" \
 b4694d887617826081439acd7c14ff3fe5e71654171e490d9174b4962c8ac8ca "$source/PA194DecoderCompleteOpen.lean" \
 df976d5c5da8b812459f67ce2128e42a608701118b4754be205743ea94a7bcb1 "$source/PA194DecoderNative.lean" \
 10479e620f643cf11aa2d1f84fd50f3f648cd634ca24cbcfb7d2290d0e94a336 "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PRAEqualityToIPRA.lean" | sha256sum -c -
 python3 - "$dispatch" "$receipt" "$base" "$project" <<'PY'
import hashlib,json,pathlib,sys
dispatch,receipt,base,project=map(pathlib.Path,sys.argv[1:])
expected=json.loads(receipt.read_text()); objects={p.name for p in dispatch.glob('*.olean')}
if len(objects)!=26 or objects!=set(expected): raise SystemExit('dispatch object set changed')
for name,h in expected.items():
 p=dispatch/name
 if p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=h: raise SystemExit('changed dispatch object: '+name)
entries=json.loads((base/'source-closure.json').read_text())
if len(entries)!=270: raise SystemExit('wrong source closure size')
for e in entries:
 p=pathlib.Path(e['source']); obj=base.joinpath(*e['module'].split('.')).with_suffix('.olean')
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=e['sha256'] or not obj.is_file():
  raise SystemExit('changed or missing source closure: '+e['module'])
graph=(base/'foundation-view/DiophantineConsistency').resolve()
pins={'PRAHistoryResultGraph':'2654808e5cfba0266f38ce2ddad33987635e8e06c3934cc131eb2a475bc1eeae','PRAHistoryTrace':'4b3ea00b4fbf5790008bddc61a69d2b7bdf84551e67084219014b57bd6402db2','PRAHistoryIterator':'b359da5684d709684b25fcd7c7073804a91044fc54ae0f2bfc9b44a7b1844583','PRAHistorySingletonSequence':'e976a9cc5de9e9ca257f78e16ea444a32684ecc3cb74f4c8f0bef7fabbb1ce40','PRAHistorySingletonMembership':'85aeb8494921b2211b7c4ca01b0fce4b5153ce0839ad6bc5e087dfdbb047c45d','PRAHistoryLengthUnique':'d225bca0cd681778109ef906169e7f7a0549289635c81e2a987f3cd67aab1c58'}
real=[]
for p in graph.glob('*.olean'):
 if p.is_symlink():
  if not p.resolve().is_relative_to(project/'DiophantineConsistency'): raise SystemExit('graph symlink outside project foundation: '+str(p))
 else: real.append(p.stem)
if set(real)!=set(pins): raise SystemExit('graph namespace real-object set changed')
for name,h in pins.items():
 if hashlib.sha256((graph/(name+'.olean')).read_bytes()).hexdigest()!=h: raise SystemExit('graph hash mismatch: '+name)
print('26 dispatch objects, 270 source hashes/objects, and six graph pins checked.')
PY
}
check_inputs
mkdir -p "$out"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$dispatch:$base:$base/foundation-view:$project:$package:$lake_path"
for m in PA194IterateAddOpen PA194UnpairDrainOpen PA194UnpairDrainOpenComplete PA194DecoderRoundOpen PA194SourceReconstruct PA194DecoderSynchronizationOpen PA194DecoderClockOpen PA194DecoderCompleteOpen; do
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
 if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
 rg 'depends on axioms:' "$out/$m.log"
done
m=PRAEqualityToIPRA
echo "Checking $m"
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -o "$out/$m.olean" "$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/$m.lean" > "$out/$m.log" 2>&1
if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
rg 'depends on axioms:' "$out/$m.log"
m=PA194DecoderNative
echo "Checking $m"
lake env env LEAN_PATH="$LEAN_PATH" lean -j1 -M 7000 -R "$source" -o "$out/$m.olean" "$source/$m.lean" > "$out/$m.log" 2>&1
if rg -q 'sorryAx|declaration uses .sorry.' "$out/$m.log"; then cat "$out/$m.log"; exit 1; fi
rg 'depends on axioms:' "$out/$m.log"
for spec in PA194IterateAddOpen:iterateAdd PA194UnpairDrainOpen:runDrain PA194UnpairDrainOpenComplete:zeroXRound PA194DecoderRoundOpen:advancePositive PA194DecoderRoundOpen:advanceZero PA194SourceReconstruct:stateReconstruct PA194DecoderSynchronizationOpen:synchronization PA194DecoderClockOpen:accumulate PA194DecoderCompleteOpen:decode PA194DecoderCompleteOpen:decodeCode PRAEqualityToIPRA:nativeOfClassical PA194DecoderNative:modelSentence PA194DecoderNative:classicalPRA PA194DecoderNative:nativeIPRA; do
 module=${spec%%:*}; thm=${spec#*:}; rg -Fq "'$module.$thm' depends on axioms:" "$out/$module.log"
done
check_inputs
echo 'PASS: universally closed native iPRA site-34 to site-42 decoder equality; machine/dispatch source outputs and prebuilt foundations as documented.'
