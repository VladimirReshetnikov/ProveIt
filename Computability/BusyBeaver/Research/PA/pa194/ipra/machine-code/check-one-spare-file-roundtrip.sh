#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE ROUND_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); round=$(realpath "$4"); project=$(realpath "$5"); package=$(realpath "$6"); source_dir=$(realpath "$7"); out=$(realpath -m "$8")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$round/"* && "$round/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 3b9735f9c08d9aaefcdb2ea6388911c89c9ae9452c64ae51c925fc58d9958eb8 "$round/PA194Site28BlankExit.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  5ffd9c946e64a8a73589bc6cdbff6982e067480057276ccfdddfc82bcc936294 "$source_dir/PA194Site28CarryCell.lean" \
  e44f7fbb7eaca063a53c6f91de56e00e2b15c210cbfad7c59efcee971f597d2f "$source_dir/PA194Site28CarryFile.lean" \
  a397d5d415a58c9d7e4094bd00c06460c1acf852a3378adcb9c23051ddbf84ad "$source_dir/PA194Site28CarryCodes.lean" \
 e658d1aab6c995dfe6f93fb5b1eae8998a83a501ad4b06bcb1e137170c089bfc "$source_dir/PA194OneSpareIterate.lean" \
 a59df9e5adb0c66303ef6a7ad6320aabfad34182207562d450a8c3a1663eb4db "$source_dir/PA194OneSpareIterateSentence.lean" \
 8d1942c76672128d2c2b078bf7ca2c3f591bd19aac835c2bb0c0885caac68fb0 "$source_dir/PA194OneSpareReturn.lean" \
 2ce7184d8b3b86f42181db8ac0ddc91a227342e1dd9afcceff2e19ef635f2022 "$source_dir/PA194OneSpareRoundTrip.lean" \
 b58ee0fdc6bd2455bcc844399f7b2f62411e2017bf899f8af4b072cfce115631 "$source_dir/PA194OneSpareIdentities.lean" \
 8bfafd0d44d012815c3d9fb7259552c68d696895c45fdcf4df33f46c71fdba96 "$source_dir/PA194OneSpareFileRoundTrip.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$round" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,round,out=map(Path,sys.argv[1:5])
for root in sys.argv[5].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,round):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
for a,b in ((baseline,stage),(baseline,round),(stage,round)):
 if any((a/p.name).exists() for p in b.glob('*.olean')): raise SystemExit(f'overlapping machine objects: {a} {b}')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'round':hashes(round)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$round:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28CarryCell PA194Site28CarryFile PA194Site28CarryCodes PA194OneSpareIterate PA194OneSpareIterateSentence PA194OneSpareReturn PA194OneSpareRoundTrip PA194OneSpareIdentities PA194OneSpareFileRoundTrip; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28CarryCell.carryCell PA194Site28CarryFile.carryFile PA194Site28CarryCodes.modelTime PA194Site28CarryCodes.modelLeft PA194Site28CarryCodes.carryFileCoded PA194OneSpareIterate.modelOneBlock PA194OneSpareIterate.modelRepeatZero PA194OneSpareIterate.modelRepeatSucc PA194OneSpareIterate.carryOne PA194OneSpareIterate.modelPartialCarry PA194OneSpareIterate.modelFullCarry PA194OneSpareIterateSentence.modelSentence PA194OneSpareIterateSentence.classicalPRA PA194OneSpareIterateSentence.nativeIPRA PA194OneSpareReturn.modelFullReturn PA194OneSpareRoundTrip.roundTrip PA194OneSpareIdentities.modelSuffixRelation PA194OneSpareIdentities.modelOutputShift PA194OneSpareFileRoundTrip.outputBlockZero PA194OneSpareFileRoundTrip.roundTrip; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$round" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,round,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(round)!=expected['round']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194OneSpareFileRoundTrip.log"
echo 'One-valued-spare model-length file round trip checked.'
