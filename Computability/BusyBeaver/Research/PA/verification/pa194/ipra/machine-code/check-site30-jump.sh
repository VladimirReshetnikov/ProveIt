#!/usr/bin/env bash
set -euo pipefail
if (($# != 15)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SELECTED29_STAGE FINISH_STAGE INCREMENT29_STAGE COMPLETE28_STAGE RETURN29_STAGE PATHS29_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); codes=$(realpath "$4"); round=$(realpath "$5"); seed=$(realpath "$6"); finish=$(realpath "$7"); increment=$(realpath "$8"); complete=$(realpath "$9"); root=$(realpath "${10}"); identities=$(realpath "${11}"); project=$(realpath "${12}"); package=$(realpath "${13}"); source_dir=$(realpath "${14}"); out=$(realpath -m "${15}")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi; done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Output already exists' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 6b02f9128c7a9b042b86116f6eab2cbd65a6a0b0d069a460ddc78a63f402acbe "$codes/PA194Site28CarryCodes.olean" \
 f739d7761eee43bcb1ce3633792d8b480da5872bca616d73d274cf21735abeea "$round/PA194Site28CarryRoundTrip.olean" \
 a3ece700ceae2a806bc147841c9c3a28af6bd89407655366f9229da3d218bcac "$seed/PA194Site29SeedTailRoundTrip.olean" \
 aeed873e0631fc1c016d88f9e3dc34ef4140ac4a28e4703109af8fb94d11ce91 "$finish/PA194Path29Header.olean" \
 1028b03158b129a0d8956fc9c6fb60e660d66f1608c49c54b7e05aa93f1cc88f "$increment/PA194Site29ToIncrement.olean" \
 e538cbc314cb1a6b4cb78040f35cae3fb1679a59a2b4b03d06f4ec7b4aab31a7 "$complete/PA194Site28SeedOutput.olean" \
 a3805c21b42ec3b5f04cb5149171db4c81b850bf4ead136579d0f3ec944162f3 "$root/PA194Site29ReturnToRoot.olean" \
 d433d082424516d29f71ea4509cb978b062d0814f82aa96a4c0ea8696d19a52e "$root/PA194Site29ReturnHeader.olean" \
 4645a2eada18c3a975976f0f83a376e6a0af3b2d4ea2526850291867273157e2 "$identities/PA194Path29Input.olean" \
 87b74b07943182b3e95be6e9a861fc79bcb34a0b8a606d57f7824a0772ad11f6 "$identities/PA194Site29ReturnPath30.olean" \
 d966ae2a163c61bca4606454ad425725a3a84403050a301dfbe1e24e692e3f36 "$identities/PA194Site29OutputWithCarry.olean" | sha256sum -c -
check_sources() { printf '%s  %s\n' a11c3f60b6882da7cff391c96ca03b354d070a9859536c8cf7340cfd67b07fca "$source_dir/PA194Site30Jump.lean" | sha256sum -c -; }
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$out" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$increment" "$complete" "$root" "$identities" "$project:$package:$lake_path" <<'PY1'
from pathlib import Path
import hashlib,json,sys
out=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:12]))
for root in sys.argv[12].split(':'):
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
PY1
export LEAN_PATH="$out:$identities:$root:$complete:$increment:$finish:$seed:$round:$codes:$stage:$baseline:$project:$package:$lake_path"
module=PA194Site30Jump
lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
for report in PA194Site30Jump.prefixRun PA194Site30Jump.jumpPath30To27; do rg -q "'$report' depends on axioms:" "$out/$module.log"; done
check_sources
python3 - "$out/input-object-receipt.json" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$increment" "$complete" "$root" "$identities" <<'PY1'
from pathlib import Path
import hashlib,json,sys
receipt=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:])); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if [hashes(d) for d in roots]!=expected: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY1
cat "$out/PA194Site30Jump.log"
echo 'Site-30 to site-27 40-step physical jump checked.'
