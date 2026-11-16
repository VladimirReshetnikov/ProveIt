#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); project=$(realpath "$5"); package=$(realpath "$6"); source_dir=$(realpath "$7"); out=$(realpath -m "$8")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$codes/"* && "$codes/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  fff4d3207be6ce58212d1af29dc6a96ba71954c4a6493daada41df8f5ee946ea "$source_dir/PA194LeftZeroWriteOne.lean" \
  1d2e4ec2914435f37dc45c714447603845dff34ee95dfa809898d817371f515e "$source_dir/PA194Site28BlankExit.lean" \
  b737554a97e9948be4e330489d551d3d82b67d419b74ea6e29ea1f276ed6809b "$source_dir/PA194Site28ReturnKick.lean" \
  331c99f2b760e9a4b31bf31f0f1abe6d5283f695783fe1f1bfd9ec5fb6564113 "$source_dir/PA194Site28ReturnCarry.lean" \
  43ff441fd4e6c40e530a264db5a9237a82f826950c280cf9186e3417950f5c8c "$source_dir/PA194Site28CarryRoundTrip.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$codes" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,out=map(Path,sys.argv[1:5])
for root in sys.argv[5].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,codes):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for a,b in ((baseline,stage),(baseline,codes),(stage,codes)) for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'codes':hashes(codes)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$codes:$stage:$baseline:$project:$package:$lake_path"
for module in PA194LeftZeroWriteOne PA194Site28BlankExit PA194Site28ReturnKick PA194Site28ReturnCarry PA194Site28CarryRoundTrip; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194LeftZeroWriteOne.leftZeroWriteOne PA194Site28BlankExit.blankExit PA194Site28ReturnKick.kickReturn PA194Site28ReturnCarry.returnCarry PA194Site28CarryRoundTrip.carryLeftOdd PA194Site28CarryRoundTrip.roundTrip; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$codes" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,codes,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(codes)!=expected['codes']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site28CarryRoundTrip.log"
echo 'Site-28 blank-tail coded carry round trip checked.'
