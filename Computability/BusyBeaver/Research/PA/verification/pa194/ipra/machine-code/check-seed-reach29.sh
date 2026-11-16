#!/usr/bin/env bash
set -euo pipefail
if (($# != 13)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SEED_STAGE FINISH_STAGE COMPLETE_STAGE PRIOR_SEED_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); complete=$(realpath "$8"); prior=$(realpath "$9"); project=$(realpath "${10}"); package=$(realpath "${11}"); source_dir=$(realpath "${12}"); out=$(realpath -m "${13}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$codes/"* && "$codes/" != "$out/"* && "$out/" != "$round/"* && "$round/" != "$out/"* && "$out/" != "$seed/"* && "$seed/" != "$out/"* && "$out/" != "$finish/"* && "$finish/" != "$out/"* && "$out/" != "$complete/"* && "$complete/" != "$out/"* && "$out/" != "$prior/"* && "$prior/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 b3a198e746e92d00d9e2af31cacf14715d845f36c1239476bc11baf5c76203e8 "$stage/PA194Site28AfterCarrySeven.olean" \
 ad9dda641b3c8fe1ef1280d22e436c8b321bddeeae2f55900f4f7a72cb4ea35e "$seed/PA194Site28SeedRoundTrip.olean" \
 a37aaeb8672213339812ae37fc74def23ddb907955d516f4fdeaef2ddc32e666 "$finish/PA194Site28FinishReturn.olean" \
 bf17a5e3b0c3ed468329b4bb585b9a170993556421a71eae9cde5b3612c02dbb "$complete/PA194Site28Complete.olean" \
 030768850bad961f06a575273f5ca37767afd4da778819bfdd56a2fe57156779 "$prior/PA194SeedZeroThenPositive.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' a5bc06c6f9c485b7e8eeca1364d37963d06973c398bd2b9c541dbc1a583336b6 "$source_dir/PA194SeedReach29.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$complete" "$prior" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,finish,complete,prior,out=map(Path,sys.argv[1:10])
for root in sys.argv[10].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,codes,round,seed,finish,complete,prior):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
roots=(baseline,stage,codes,round,seed,finish,complete,prior)
if any((a/p.name).exists() for i,a in enumerate(roots) for b in roots[i+1:] for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'codes':hashes(codes),'round':hashes(round),'seed':hashes(seed),'finish':hashes(finish),'complete':hashes(complete),'prior':hashes(prior)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$prior:$complete:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
module=PA194SeedReach29
lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
for report in PA194SeedReach29.blankToSite29 PA194SeedReach29.site29Register0 PA194SeedReach29.site29Register8; do
 rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$complete" "$prior" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,finish,complete,prior,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(codes)!=expected['codes'] or hashes(round)!=expected['round'] or hashes(seed)!=expected['seed'] or hashes(finish)!=expected['finish'] or hashes(complete)!=expected['complete'] or hashes(prior)!=expected['prior']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194SeedReach29.log"
echo 'Blank-tape-to-site-29 model-uniform finite execution checked.'
