#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); source_dir=$(realpath "$8"); out=$(realpath -m "$9")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$codes/"* && "$codes/" != "$out/"* && "$out/" != "$round/"* && "$round/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 b3a198e746e92d00d9e2af31cacf14715d845f36c1239476bc11baf5c76203e8 "$stage/PA194Site28AfterCarrySeven.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  88e92a9b07d46e57e210b45931e1daacba58685407a2f79dc17f17aae95c3fb1 "$source_dir/PA194Site28SeedTail.lean" \
  60880f6b4c8070140e0a94eafa23546ffce6ccc8ea20e4a2f2fe38783b26dee6 "$source_dir/PA194Path28Input.lean" \
  31d93a371baa285d8b50596b2fa00a33e4080e3dbf16fa1445de0843c49ec53b "$source_dir/PA194Site28SeedTailRoundTrip.lean" \
  53236b76380c3166a052363047c07469348476e47db89c055f44b68d3a6c0564 "$source_dir/PA194Site28SeedRoundTrip.lean" \
 6963ec0cab692f24d80ee8c670a2f00b2c264ca51c0cdc052573fd3e1bb25d5b "$source_dir/PA194Site29SeedTailRoundTrip.lean" \
 f913178e89c68243aa90a159611329a29f9b333b42ae57666d1e81f1e1cd2121 "$source_dir/PA194Site29ReturnNext.lean" \
 bb59708beb97ee5af7e0482b0167d09e35d01c52e611f54704004fd345e3b0ce "$source_dir/PA194Site29SelectedReturn.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$codes" "$round" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,out=map(Path,sys.argv[1:6])
for root in sys.argv[6].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,codes,round):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for a,b in ((baseline,stage),(baseline,codes),(stage,codes),(baseline,round),(stage,round),(codes,round)) for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'codes':hashes(codes),'round':hashes(round)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28SeedTail PA194Path28Input PA194Site28SeedTailRoundTrip PA194Site28SeedRoundTrip PA194Site29SeedTailRoundTrip PA194Site29ReturnNext PA194Site29SelectedReturn; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28SeedTail.natFileSeedTail PA194Site28SeedTail.modelFileSeedTail PA194Path28Input.site28Input PA194Site28SeedTailRoundTrip.seedTailRoundTrip PA194Site28SeedRoundTrip.rootToState3 PA194Site28SeedRoundTrip.markedOdd PA194Site28SeedRoundTrip.rootToSeedReturn PA194Site29SeedTailRoundTrip.seedTailRoundTrip PA194Site29ReturnNext.returnNext PA194Site29ReturnNext.returnPrevious PA194Site29SelectedReturn.selectedReturn; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$codes" "$round" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(codes)!=expected['codes'] or hashes(round)!=expected['round']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site29SelectedReturn.log"
echo 'Site-29 extended seed-tail carry and selected-register return checked.'
