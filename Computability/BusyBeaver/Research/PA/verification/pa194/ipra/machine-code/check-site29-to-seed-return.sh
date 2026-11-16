#!/usr/bin/env bash
set -euo pipefail
if (($# != 12)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SEED29_STAGE FINISH_STAGE INCREMENT29_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); increment=$(realpath "$8"); project=$(realpath "$9"); package=$(realpath "${10}"); source_dir=$(realpath "${11}"); out=$(realpath -m "${12}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 f7d465a85b49f1c06f11f1e36168e6363b5903e77bd33e66d44fd201bb7187f7 "$codes/PA194Site28CarryCell.olean" \
 2b28409381240e6a0134723c456ab2c1f137114194f53c25ff20e950eb791212 "$codes/PA194Site28CarryFile.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 a3ece700ceae2a806bc147841c9c3a28af6bd89407655366f9229da3d218bcac "$seed/PA194Site29SeedTailRoundTrip.olean" \
 aeed873e0631fc1c016d88f9e3dc34ef4140ac4a28e4703109af8fb94d11ce91 "$finish/PA194Path29Header.olean" \
 1028b03158b129a0d8956fc9c6fb60e660d66f1608c49c54b7e05aa93f1cc88f "$increment/PA194Site29ToIncrement.olean" | sha256sum -c -
check_source() { printf '%s  %s\n' b91a5615c8bb793a96c60b7ede14fae1c47dc2bcc389e567996ed8812ce82786 "$source_dir/PA194Site29ToSeedReturnFast.lean" | sha256sum -c -; }
check_source
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$out" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$increment" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
out=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:9]))
for root in sys.argv[9].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in roots:
 if out in d.parents or d in out.parents or out==d: raise SystemExit(f'input/output overlap: {d}')
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for i,a in enumerate(roots) for b in roots[i+1:] for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between inputs')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps([hashes(d) for d in roots],indent=2)+'\n')
print('Recorded all input object hashes.',flush=True)
PY
export LEAN_PATH="$out:$increment:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
module=PA194Site29ToSeedReturnFast
lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
rg -q "'PA194Site29ToSeedReturnFast.site29ToSeedReturn' depends on axioms:" "$out/$module.log"
check_source
python3 - "$out/input-object-receipt.json" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$increment" <<'PY'
from pathlib import Path
import hashlib,json,sys
receipt=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:])); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if [hashes(d) for d in roots]!=expected: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/$module.log"
echo 'Site-29 root to state-7 seed-tail carry return checked.'
