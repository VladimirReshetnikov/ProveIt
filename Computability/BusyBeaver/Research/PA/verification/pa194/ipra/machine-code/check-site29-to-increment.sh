#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE FINISH_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); finish=$(realpath "$4"); project=$(realpath "$5"); package=$(realpath "$6"); source_dir=$(realpath "$7"); out=$(realpath -m "$8")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* && "$out/" != "$stage/"* && "$stage/" != "$out/"* && "$out/" != "$finish/"* && "$finish/" != "$out/"* ]] || { echo 'Existing output or input/output overlap' >&2; exit 2; }
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 43793b7255afe3ef728cd0218792104168160cd88c505c6f4ac25a1d1b7fffde "$stage/PA194Site28To84.olean" \
 a98d9b6007c6560058c7196659899bebbda17080ef526d35dee66227f7112286 "$stage/PA194Site28HeaderReturnPrefix.olean" \
 b8e14c7f22e042abd29433393c73283735f4ed3d91f8a9cd539c9e9b25d5e590 "$stage/PA194Site28SecondReturn.olean" \
 aeed873e0631fc1c016d88f9e3dc34ef4140ac4a28e4703109af8fb94d11ce91 "$finish/PA194Path29Header.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  c6401f77958aaa7212ca887d77fc4c77ddbab6847a00d852fcf36cdc6a7ee248 "$source_dir/PA194Site29HeaderDispatch.lean" \
  d2d2bcb7b8529cb90b9a304588f57fc0dd956465933032cf5b1a985f85774f05 "$source_dir/PA194Site29To84.lean" \
  124ebdcd87924e3d9eb8664b1777cdb74b4fa57073851c9b778ea121a4b10470 "$source_dir/PA194Site29HeaderTo17.lean" \
  006872b330b1e3b42ba9fd39fbada333076f968b5f84726813c2b8c031d89549 "$source_dir/PA194Site29HeaderReturn.lean" \
  af96e979a1f617405ae43c5de96bd1dcf7a6639572327b24227adc9de341eb9a "$source_dir/PA194Site29HeaderPass.lean" \
 cce9969cabf7ddfd720c6bef5290f3b08fb5e22b30089c3edb938fa86466260e "$source_dir/PA194Site29SecondDispatch.lean" \
 5a12a2000b6b964c5560766ab1266e2e1e790083d161abc2d5f3c5a9924bcef2 "$source_dir/PA194Site29ScanTo71.lean" \
 52c2a1219a46cbbf2fb771bc64725bc4a7cceb228a9ad0de333c5b580d1d869d "$source_dir/PA194Site29SecondPassTo71.lean" \
 8ee095cdde8052ee40c43efccae74475822ff482312b4fc47b1c4b91bb1c3836 "$source_dir/PA194Site29TwoPassesTo71.lean" \
 a42e1b68f73cea835315523ef443be460b23034890ff99425638b393fa353549 "$source_dir/PA194ScanSixRewindWithTail.lean" \
 9fb633a4794cead1e127b4887245a829aed62cda176ac0743b0bebdd4e0eb758 "$source_dir/PA194Site29ScanRewind.lean" \
 8ebe5242f25b0284516718ef6f154085906e64bb3516def087a18fc83e8ef610 "$source_dir/PA194Site29To17.lean" \
 391eebd31191e9a267f3c3c2827662d05f504e4cb21090f3a04efe7541e9e27e "$source_dir/PA194Site29ReturnThree.lean" \
 b64970975c5384da34a50ecd428a7ae4e338d0015f495bfef46cbfc3d662e4c0 "$source_dir/PA194Site29ReturnToHeader.lean" \
 719e4c1459cf2d759b77c3ad77eb8609b5fa97e2e76da4e5dc30e49a4758e654 "$source_dir/PA194Site29HeaderBackTo24.lean" \
 bf1728e65bb5ba64905b27b054193fbec8e79dc77458cdb5130fe64bcb98fbc2 "$source_dir/PA194Site29SecondRoot.lean" \
 9e0a333c678679d57e1d644deae606d2fd2c1b67a06cdb0a149065d1bdc73bd5 "$source_dir/PA194Site29ThirdDispatch.lean" \
 b6aa72280480bf81cb25e5c2af73ee00133fc9788c173eb503b6f7a45dd4d0c1 "$source_dir/PA194Site29To2.lean" \
 594c5a8c1d4abed2da37a4198dd4f771dd366c74f15ea4b4ffb7638b27591c60 "$source_dir/PA194Site29TwoBlock.lean" \
 d0639f2b753ed45af769375211dc70cef2e71e3b4abbab33627a9b6cd36b808c "$source_dir/PA194Site29TwoFile.lean" \
 dd24aba51be227905d4b01c549252b9402e5aad9c1ac8b0277989fe4236d658a "$source_dir/PA194Site29ScanTo1.lean" \
 ddb04399a0a45dd7757d8380c07fcd599037ce52c85a81c623d3995946caf815 "$source_dir/PA194Site29ThirdToIncrement.lean" \
 31637ae18a837c07d5a14519f6084f9655a4db00a9b6d91d6f140a0b2a235e71 "$source_dir/PA194Site29ToIncrement.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$finish" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,finish,out=map(Path,sys.argv[1:5])
for root in sys.argv[5].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in (baseline,stage,finish):
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
if any((a/p.name).exists() for a,b in ((baseline,stage),(baseline,finish),(stage,finish)) for p in b.glob('*.olean')): raise SystemExit('overlapping machine objects between stage and baseline')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir(); (out/'input-object-receipt.json').write_text(json.dumps({'baseline':hashes(baseline),'stage':hashes(stage),'finish':hashes(finish)},indent=2)+'\n')
print('Recorded baseline and stage object hashes.',flush=True)
PY
export LEAN_PATH="$out:$finish:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site29HeaderDispatch PA194Site29To84 PA194Site29HeaderTo17 PA194Site29HeaderReturn PA194Site29HeaderPass PA194Site29SecondDispatch PA194Site29ScanTo71 PA194Site29SecondPassTo71 PA194Site29TwoPassesTo71 PA194ScanSixRewindWithTail PA194Site29ScanRewind PA194Site29To17 PA194Site29ReturnThree PA194Site29ReturnToHeader PA194Site29HeaderBackTo24 PA194Site29SecondRoot PA194Site29ThirdDispatch PA194Site29To2 PA194Site29TwoBlock PA194Site29TwoFile PA194Site29ScanTo1 PA194Site29ThirdToIncrement PA194Site29ToIncrement; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site29HeaderDispatch.eightSteps PA194Site29To84.elevenTo84 PA194Site29To84.nineteenTo84 PA194Site29HeaderTo17.site29HeaderTo17 PA194Site29HeaderReturn.sevenTo19 PA194Site29HeaderReturn.returnTo24 PA194Site29HeaderPass.site29HeaderPass PA194Site29SecondDispatch.eighteenTo60 PA194Site29ScanTo71.scanTo71 PA194Site29SecondPassTo71.secondPassTo71 PA194Site29TwoPassesTo71.twoPassesTo71 PA194ScanSixRewindWithTail.scanAndRewind PA194Site29ScanRewind.scanAndRewind PA194Site29To17.site29To17 PA194Site29ReturnThree.returnThree PA194Site29ReturnToHeader.site29ReturnToHeader PA194Site29HeaderBackTo24.eightTo19 PA194Site29HeaderBackTo24.returnTo24 PA194Site29SecondRoot.site29SecondRoot PA194Site29ThirdDispatch.elevenTo2 PA194Site29ThirdDispatch.nineteenTo2 PA194Site29ThirdDispatch.rootTo2 PA194Site29To2.site29To2 PA194Site29TwoBlock.traverse PA194Site29TwoBlock.fileHop PA194Site29TwoFile.traverseFile PA194Site29ScanTo1.scanTo1 PA194Site29ThirdToIncrement.thirdToIncrement PA194Site29ToIncrement.site29ToIncrement; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$finish" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,stage,finish,receipt=map(Path,sys.argv[1:]); expected=json.loads(receipt.read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if hashes(baseline)!=expected['baseline'] or hashes(stage)!=expected['stage'] or hashes(finish)!=expected['finish']: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194Site29ToIncrement.log"
echo 'Site-29 model-uniform execution through selected-register increment checked.'
