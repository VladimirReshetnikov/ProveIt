#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo 'usage: REPO UNIFIED_BASELINE PROJECT PACKAGE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); project=$(realpath "$3"); package=$(realpath "$4"); out=$(realpath -m "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* ]] || { echo 'Existing output or baseline/output overlap' >&2; exit 2; }
printf '%s  %s\n' d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" | sha256sum -c -
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,shutil,sys
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
shutil.copytree(baseline,out,copy_function=shutil.copy2)
for rel,digest in before.items():
 a=baseline/rel; b=out/rel
 if a.stat().st_ino==b.stat().st_ino and a.stat().st_dev==b.stat().st_dev: raise SystemExit(f'copy retained baseline inode: {rel}')
 if sha(a)!=digest or sha(b)!=digest: raise SystemExit(f'baseline changed or copy mismatch: {rel}')
(out/'site27-baseline-object-receipt.json').write_text(json.dumps({'baseline':str(baseline),'object_sha256':before},indent=2)+'\n')
print(f'Staged {len(before)} independent matching objects',flush=True)
PY
export LEAN_PATH="$out:$project:$package:$lake_path"
python3 "$(dirname "$0")/build-site27-coherent.py" --repo "$repo" --out "$out" --jobs "${PA194_SITE27_JOBS:-2}"
