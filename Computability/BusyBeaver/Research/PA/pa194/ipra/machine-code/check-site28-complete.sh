#!/usr/bin/env bash
set -euo pipefail
if (($# != 11)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SEED_STAGE FINISH_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); project=$(realpath "$8"); package=$(realpath "$9"); source_dir=$(realpath "${10}"); out=$(realpath -m "${11}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$codes/"* && "$codes/" != "$out/"* && "$out/" != "$round/"* && "$round/" != "$out/"* && "$out/" != "$seed/"* && "$seed/" != "$out/"* && "$out/" != "$finish/"* && "$finish/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 b3a198e746e92d00d9e2af31cacf14715d845f36c1239476bc11baf5c76203e8 "$stage/PA194Site28AfterCarrySeven.olean" \
 ad9dda641b3c8fe1ef1280d22e436c8b321bddeeae2f55900f4f7a72cb4ea35e "$seed/PA194Site28SeedRoundTrip.olean" \
 a37aaeb8672213339812ae37fc74def23ddb907955d516f4fdeaef2ddc32e666 "$finish/PA194Site28FinishReturn.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  3b72da0ff31752573e349ef62f750f8e6e382a560d081b4961aec0843fad0bc3 "$source_dir/PA194Site28SeedOutputProbe.lean" \
  1c12af3a1a7841adfba760909b602dd2a0e376c6a1ab9a8eb635ba4eb99cd25e "$source_dir/PA194Site28SeedOutput.lean" \
  dcc652f228fc65a9cb8f8bc6c63ea7399b9d4a809e7bf9891edf5263cd0f432b "$source_dir/PA194Site28OutputFile.lean" \
  9c12df9efd7d9002d9acad902942a0dc1f32536f8c7ea76c6342bb0a16dbdd28 "$source_dir/PA194Site28Complete.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,finish,out=map(Path,sys.argv[1:8])
for root in sys.argv[8].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,codes,round,seed,finish):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for a,b in ((baseline,stage),(baseline,codes),(stage,codes),(baseline,round),(stage,round),(codes,round),(baseline,seed),(stage,seed),(codes,seed),(round,seed),(baseline,finish),(stage,finish),(codes,finish),(round,finish),(seed,finish)) for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'codes':hashes(codes),'round':hashes(round),'seed':hashes(seed),'finish':hashes(finish)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28SeedOutputProbe PA194Site28SeedOutput PA194Site28OutputFile PA194Site28Complete; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28SeedOutputProbe.probe PA194Site28SeedOutput.fixedTail PA194Site28SeedOutput.tailBase PA194Site28SeedOutput.seedReturnFile PA194Site28OutputFile.returnAppendBlock PA194Site28OutputFile.outputFile PA194Site28Complete.complete; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,round,seed,finish,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(codes)!=expected['codes'] or hashes(round)!=expected['round'] or hashes(seed)!=expected['seed'] or hashes(finish)!=expected['finish']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site28Complete.log"
echo 'Site-28 complete finite-tail source increment checked.'
