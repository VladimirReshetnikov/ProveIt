#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then
  echo "usage: $0 REPO HEADER_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION NEW_OUTPUT" >&2
  exit 2
fi
repo=$(realpath "$1")
baseline=$(realpath "$2")
project=$(realpath "$3")
package=$(realpath "$4")
out=$(realpath -m "$5")
script_dir=$(cd "$(dirname "$0")" && pwd)
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
if [[ ! -d "$project" || ! -d "$package" ]]; then echo "Missing foundation root" >&2; exit 2; fi
if [[ -e "$out" || -L "$out" ]]; then echo "Refusing existing output: $out" >&2; exit 2; fi
if [[ "$out/" == "$baseline/"* || "$baseline/" == "$out/"* ]]; then echo 'Baseline/output overlap' >&2; exit 2; fi
printf '%s  %s\n' 24cb6eca676a5a6d74c4ac4a96b4d611b618c907f6b9a698f21a62c088640cc4 "$baseline/header-coherent-manifest.json" | sha256sum -c -
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$repo" "$baseline" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,shutil,sys
repo,baseline,out=map(Path,sys.argv[1:4])
roots=sys.argv[4].split(':')
for root in roots:
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue  # Lake may list absent optional package roots.
 for pattern in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pattern)): raise SystemExit(f'machine-specific fallback in {root}: {pattern}')
if any(p.is_symlink() for p in baseline.rglob('*')):
 raise SystemExit('refusing baseline with symlinks')
manifest=json.loads((baseline/'header-coherent-manifest.json').read_text())
source=repo/'Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code'
extra=repo/'Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-command-source/PA194FetchPrefixBinding.lean'
for name,digest in manifest['new_sources_sha256'].items():
 p=extra if name=='PA194FetchPrefixBinding' else source/(name+'.lean')
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
  raise SystemExit(f'baseline manifest source mismatch: {name}')
objs=sorted(p for p in baseline.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(baseline)):sha(p) for p in objs}
shutil.copytree(baseline,out,copy_function=shutil.copy2)
for rel,digest in before.items():
 a=baseline/rel; b=out/rel
 if a.stat().st_ino==b.stat().st_ino and a.stat().st_dev==b.stat().st_dev:
  raise SystemExit(f'copy retained baseline inode: {rel}')
 if sha(a)!=digest or sha(b)!=digest: raise SystemExit(f'baseline changed or copy mismatch: {rel}')
(out/'baseline-object-receipt.json').write_text(json.dumps({'baseline':str(baseline),'object_sha256':before},indent=2)+'\n')
print(f'Staged {len(before)} identical independent baseline objects.',flush=True)
PY
export LEAN_PATH="$out:$project:$package:$lake_path"
python3 "$script_dir/build-unified-coherent.py" --repo "$repo" --out "$out" --jobs "${PA194_UNIFIED_JOBS:-2}"
