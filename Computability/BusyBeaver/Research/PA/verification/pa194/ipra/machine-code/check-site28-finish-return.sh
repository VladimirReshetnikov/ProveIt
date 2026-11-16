#!/usr/bin/env bash
set -euo pipefail
if (($# != 10)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SEED_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); project=$(realpath "$7"); package=$(realpath "$8"); source_dir=$(realpath "$9"); out=$(realpath -m "${10}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$codes/"* && "$codes/" != "$out/"* && "$out/" != "$round/"* && "$round/" != "$out/"* && "$out/" != "$seed/"* && "$seed/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 b3a198e746e92d00d9e2af31cacf14715d845f36c1239476bc11baf5c76203e8 "$stage/PA194Site28AfterCarrySeven.olean" \
 ad9dda641b3c8fe1ef1280d22e436c8b321bddeeae2f55900f4f7a72cb4ea35e "$seed/PA194Site28SeedRoundTrip.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  35e65ae1088fa3ee694ffe5511c76ad2aad71aebac1e6a29fa550d9569a5780e "$source_dir/PA194Site28ReturnSelected.lean" \
  6b596e80c021c6a833d8d5ff66bcb57dcf5ff5b3eeea2ce142b9e082011b2c57 "$source_dir/PA194Site28ReturnHeader.lean" \
  c14a73a7fc3158cfc68a59d0bba4d765dbb8f2f719b9c3d040a44eb7eb9bc543 "$source_dir/PA194Path29Header.lean" \
  fe378c3315bfab570d24953534ea018dcfe8f715e19911d800056bc0a151ced9 "$source_dir/PA194Site28HeaderTo29.lean" \
  cb1adc6776b5a9d3b862e994ea3325cab69cc589ee4f31ea5dd3e120724a38f7 "$source_dir/PA194Site28FinishReturn.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,out=map(Path,sys.argv[1:7])
for root in sys.argv[7].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,codes,round,seed):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for a,b in ((baseline,stage),(baseline,codes),(stage,codes),(baseline,round),(stage,round),(codes,round),(baseline,seed),(stage,seed),(codes,seed),(round,seed)) for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'codes':hashes(codes),'round':hashes(round),'seed':hashes(seed)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28ReturnSelected PA194Site28ReturnHeader PA194Path29Header PA194Site28HeaderTo29 PA194Site28FinishReturn; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28ReturnSelected.returnSelected PA194Site28ReturnHeader.headerTo24 PA194Path29Header.path29 PA194Path29Header.resultIsPath29 PA194Site28HeaderTo29.headerTo29 PA194Site28FinishReturn.marked_eq PA194Site28FinishReturn.initialMarkOdd PA194Site28FinishReturn.finishReturn; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(codes)!=expected['codes'] or hashes(round)!=expected['round'] or hashes(seed)!=expected['seed']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site28FinishReturn.log"
echo 'Site-28 state-7 to site-29 control return checked.'
