#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then echo 'usage: REPO SITE27_BASELINE PROJECT PACKAGE SOURCE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); project=$(realpath "$3"); package=$(realpath "$4"); source=$(realpath "$5"); out=$(realpath -m "$6")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* ]] || { echo 'Existing output or baseline/output overlap' >&2; exit 2; }
printf '%s  %s\n' 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" c28addab1ddd579201aa2fbf39eb383f41c9843c1d8f417ea723b5503c2cd621 "$source" | sha256sum -c -
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
lean -M6000 -j1 -R "$(dirname "$source")" -o "$out/PA194Site27PositiveSentence.olean" "$source" > "$out/lean.log" 2>&1
for theorem in modelSentence classicalPRA nativeIPRA; do
  rg -q "'PA194Site27PositiveSentence.$theorem' depends on axioms:" "$out/lean.log"
done
if rg -q 'sorryAx' "$out/lean.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
printf '%s  %s\n' c28addab1ddd579201aa2fbf39eb383f41c9843c1d8f417ea723b5503c2cd621 "$source" | sha256sum -c -
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
cat "$out/lean.log"
echo 'Site-27 native positive sentence checked.'
