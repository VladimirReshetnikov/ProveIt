#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); project=$(realpath "$4"); package=$(realpath "$5"); source_dir=$(realpath "$6"); out=$(realpath -m "$7")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  5ffd9c946e64a8a73589bc6cdbff6982e067480057276ccfdddfc82bcc936294 "$source_dir/PA194Site28CarryCell.lean" \
  e44f7fbb7eaca063a53c6f91de56e00e2b15c210cbfad7c59efcee971f597d2f "$source_dir/PA194Site28CarryFile.lean" \
  a397d5d415a58c9d7e4094bd00c06460c1acf852a3378adcb9c23051ddbf84ad "$source_dir/PA194Site28CarryCodes.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,out=map(Path,sys.argv[1:4])
for root in sys.argv[4].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((baseline/p.name).exists() for p in stage.glob('*.olean')): raise SystemExit('overlapping machine objects between stage and baseline')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28CarryCell PA194Site28CarryFile PA194Site28CarryCodes; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28CarryCell.carryCell PA194Site28CarryFile.carryFile PA194Site28CarryCodes.modelTime PA194Site28CarryCodes.modelLeft PA194Site28CarryCodes.carryFileCoded; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site28CarryCodes.log"
echo 'Site-28 coded carry family checked.'
