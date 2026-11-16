#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then echo 'usage: REPO SITE27_BASELINE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); project=$(realpath "$3"); package=$(realpath "$4"); source_dir=$(realpath "$5"); out=$(realpath -m "$6")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* ]] || { echo 'Existing output or baseline/output overlap' >&2; exit 2; }
printf '%s  %s\n' 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
 f3a049bd168f5f60a91d651efa94347f6755b6e0f00d2c2fd61f911951f022b0 "$source_dir/PA194Site28HeaderDispatch.lean" \
 d73e4d3e8816cf88015603f60be51d7343eeb6bfc24232b5c6bc710c2bc4e495 "$source_dir/PA194Site28To84.lean" \
 d9724e26cb9552bab43f80af1789d8cdc18778fbf72451cc03aad0910031ebaa "$source_dir/PA194Site28HeaderTo17.lean" \
 46359a15ed8c059fb693bcf650671b572d10cc6daf92c20566e4a6a814e7bc98 "$source_dir/PA194Site28HeaderReturnPrefix.lean" \
 07ec4c66391b672747e37419e450d213a33f492f65ea73a91b435517d1b25134 "$source_dir/PA194Site28HeaderReturn.lean" \
 a8cded984ff66afb76c133f0d5facf6f45c5ea9c4b7f2345bd1e1a8f9106cbc4 "$source_dir/PA194Site28HeaderPass.lean" \
 7cefe2b93f8e7f7377420ffa9fe7f81683e3cf160dd333015c0c4ced15fa0b17 "$source_dir/PA194Site28SecondDispatch.lean" \
 139938065100f7ea586336f71367683c6896f812a9c487b8694f749df411f82a "$source_dir/PA194Site28SecondReturn.lean" \
 8a054643be0a4a2bee2f96771453c83e52894ecb84860b0960a62cb6ef720a8d "$source_dir/PA194Site28SecondPass.lean" \
 2a1a2b5f6bb8bb927a5bc0e2255af0ebca3ed9db3359971a7799dbbc9328107c "$source_dir/PA194Site28TwoPasses.lean" \
 4ec5b644916f23b240f84b3e6e51931fd4e20f80950291b30e1955f30b1bde2f "$source_dir/PA194Site28ThirdDispatch.lean" \
 a3da14ea5fd0ba1cea6863078a5cc7f5c9a6e998dedde60e4008c3243a158724 "$source_dir/PA194Site28TwoPassesTo2.lean" \
 0b7eb6decdd4caef88e76f6387b8ea6824462adfba1cbeae5ba147d52d919173 "$source_dir/PA194Site28ScanTo1.lean" \
 1a3b61b8afd1a929fe2a937bf51b9f3d78ff5f03b0c806f8d93702f81cf98e67 "$source_dir/PA194Site28TwoPassesTo1.lean" \
 9565d5637e3159da55a0a8f847f1c48771d040b2e6c87a689cb917244e5ff74b "$source_dir/PA194Site28IncrementWrite.lean" \
 7b8c1ec58924cae2d19964a25e92854f27dab6e3b10f0762ec4991667aa6f162 "$source_dir/PA194Site28ToIncrement.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
baseline,out=map(Path,sys.argv[1:3])
for root in sys.argv[3].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
if any(p.is_symlink() for p in baseline.rglob('*')): raise SystemExit('symlink in baseline')
objs=sorted(p for p in baseline.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(baseline)):sha(p) for p in objs}
out.mkdir()
(out/'baseline-object-receipt.json').write_text(json.dumps({'baseline':str(baseline),'object_sha256':before},indent=2)+'\n')
print(f'Recorded {len(before)} baseline object hashes.',flush=True)
PY
export LEAN_PATH="$out:$baseline:$project:$package:$lake_path"
for module in PA194Site28HeaderDispatch PA194Site28To84 PA194Site28HeaderTo17 PA194Site28HeaderReturnPrefix PA194Site28HeaderReturn PA194Site28HeaderPass PA194Site28SecondDispatch PA194Site28SecondReturn PA194Site28SecondPass PA194Site28TwoPasses PA194Site28ThirdDispatch PA194Site28TwoPassesTo2 PA194Site28ScanTo1 PA194Site28TwoPassesTo1 PA194Site28IncrementWrite PA194Site28ToIncrement; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28HeaderDispatch.eightSteps PA194Site28To84.sixteenSteps PA194Site28HeaderTo17.site28HeaderTo17 PA194Site28HeaderReturnPrefix.fourReturnSteps PA194Site28HeaderReturn.returnTo24 PA194Site28HeaderPass.site28HeaderPass PA194Site28SecondDispatch.nineTo93 PA194Site28SecondReturn.sevenTo19 PA194Site28SecondPass.secondPass PA194Site28TwoPasses.twoPasses PA194Site28ThirdDispatch.sixteenTo2 PA194Site28TwoPassesTo2.twoPassesTo2 PA194Site28ScanTo1.scanTo1 PA194Site28TwoPassesTo1.twoPassesTo1 PA194Site28IncrementWrite.incrementWrite PA194Site28ToIncrement.toIncrement; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$out/baseline-object-receipt.json" <<'PYEND'
from pathlib import Path
import hashlib,json,sys
baseline,receipt=map(Path,sys.argv[1:])
expected=json.loads(receipt.read_text())['object_sha256']
actual={str(p.relative_to(baseline)):hashlib.sha256(p.read_bytes()).hexdigest()
 for p in baseline.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if actual != expected: raise SystemExit('baseline objects changed during replay')
print(f'Verified {len(expected)} unchanged baseline objects.',flush=True)
PYEND
cat "$out/PA194Site28ToIncrement.log"
echo 'Site-28 model-uniform physical increment write checked.'
