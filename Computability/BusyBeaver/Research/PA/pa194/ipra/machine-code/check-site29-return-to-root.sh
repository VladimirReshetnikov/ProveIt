#!/usr/bin/env bash
set -euo pipefail
if (($# != 12)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE CODE_STAGE ROUND_STAGE SELECTED29_STAGE FINISH_STAGE INCREMENT29_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
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
 f281ff7d46239bc35a520ea82c75dc99714ad5954383227dec2843583715f7f3 "$seed/PA194Site29ReturnNext.olean" \
 a41249295de1d49b4fafc765d6584655481ce861f6f78c52cf88d6f3b9756865 "$seed/PA194Site29SelectedReturn.olean" \
 aeed873e0631fc1c016d88f9e3dc34ef4140ac4a28e4703109af8fb94d11ce91 "$finish/PA194Path29Header.olean" \
 1028b03158b129a0d8956fc9c6fb60e660d66f1608c49c54b7e05aa93f1cc88f "$increment/PA194Site29ToIncrement.olean" | sha256sum -c -
check_source() { printf '%s  %s\n' \
 6cc36fd991dedd7f3ca239a593bbb09826154e6002c395f5d26d3e0677bcc8f8 "$source_dir/PA194Site29ReturnNormalized.lean" \
 928a7913b3fec23b8b1ac25091ea746262fca45438dc272129dcdf8f91bb0e93 "$source_dir/PA194Site29ReturnSixFast.lean" \
 ba4a6dadd5e2212a5010934712a82589175538d08b85973e4513d625d89716b6 "$source_dir/PA194Site29ReturnSixFromSelected.lean" \
 b0d3f2cd8395a8287ae8d0de58798f3da40b393513c7d14f1db707e0ae5a4f9b "$source_dir/PA194Site29SelectedAndSix.lean" \
 9898e67102d750f7a89d3f2895fda45a8c39e33ac98affe03f1c755ad8366ab8 "$source_dir/PA194Site29ReturnFinalBlocks.lean" \
 c312b69892e635ca06fcbfb0ab7c7838316ed633efa0a80691a9e4c4083e0f8a "$source_dir/PA194Site29ReturnAllBlocks.lean" \
 a3d3a55c3f093a4ef3b196b8ed24560262c5ac9748e4593d78d36ada05a59a60 "$source_dir/PA194Site29ReturnFileToHeader.lean" \
 8f193d3a288975b36452be71a4d4ab82b01688320b2ae2d8697fa745e9f13409 "$source_dir/PA194Site29ReturnHeader.lean" \
 a9a6fcd6fb19c06db5aa2e1a3bab0a44a0ce8396b9ee2f4d805a54ae6a8d7980 "$source_dir/PA194Site29ReturnToRoot.lean" | sha256sum -c -; }
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
for module in PA194Site29ReturnNormalized PA194Site29ReturnSixFast PA194Site29ReturnSixFromSelected PA194Site29SelectedAndSix PA194Site29ReturnFinalBlocks PA194Site29ReturnAllBlocks PA194Site29ReturnFileToHeader PA194Site29ReturnHeader PA194Site29ReturnToRoot; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site29ReturnNormalized.returnPrevious PA194Site29ReturnSixFast.returnSix PA194Site29ReturnSixFromSelected.sixFromSelected PA194Site29SelectedAndSix.selectedAndSix PA194Site29ReturnFinalBlocks.returnOdd PA194Site29ReturnFinalBlocks.returnEven PA194Site29ReturnFinalBlocks.remainingReturn PA194Site29ReturnAllBlocks.returnAllBlocks PA194Site29ReturnFileToHeader.returnFileToHeader PA194Site29ReturnHeader.headerTo24 PA194Site29ReturnToRoot.returnToRoot; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_source
python3 - "$out/input-object-receipt.json" "$baseline" "$stage" "$codes" "$round" "$seed" "$finish" "$increment" <<'PY'
from pathlib import Path
import hashlib,json,sys
receipt=Path(sys.argv[1]); roots=list(map(Path,sys.argv[2:])); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if [hashes(d) for d in roots]!=expected: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site29ReturnToRoot.log"
echo 'Site-29 state-3 seed-tail carry and return to state-24 root checked.'
