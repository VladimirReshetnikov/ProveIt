#!/usr/bin/env bash
set -euo pipefail
if (($# != 8)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE ROUNDTRIP_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); roundtrip=$(realpath "$4"); project=$(realpath "$5"); package=$(realpath "$6"); source_dir=$(realpath "$7"); out=$(realpath -m "$8")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Existing output' >&2; exit 2; }
for d in "$baseline" "$stage" "$roundtrip"; do
 [[ "$out/" != "$d/"* && "$d/" != "$out/"* ]] || { echo 'Overlapping output/input' >&2; exit 2; }
done
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 b209cd050545f75a761c95e2cfa08aac734181af8e85426359c15bffd95ec777 "$roundtrip/PA194OneSpareIterate.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' b0c4f50a0f5e8cdd915125fce3a5265de44e51846f182793b753c19dbf5f05ab "$source_dir/PA194ModelLoopIteration.lean" \
 a700635165680c80d9ad6e7f83d59b2945122b8e39cc59d7f7fa130a4e603ad4 "$source_dir/PA194ModelLoopState.lean" \
 faad42fb3d1b325f964b17bc7e4fbbcae295d7d0327ab00f7f983dff530cbd90 "$source_dir/PA194ModelLoopFrame.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$roundtrip" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
roots=list(map(Path,sys.argv[1:4]));out=Path(sys.argv[4])
for root in sys.argv[5].split(':'):
 p=Path(root)
 if not root: raise SystemExit('empty search root')
 if not p.is_dir(): continue
 for pat in ('PA19*.olean','Packed*.olean','BinaryTape*.olean','Configuration*.olean','TableDispatch*.olean','PRAEquality*.olean','M6'):
  if any(p.glob(pat)): raise SystemExit(f'machine-specific fallback {root}: {pat}')
for d in roots:
 if any(p.is_symlink() for p in d.rglob('*')): raise SystemExit(f'symlink in input {d}')
for i,a in enumerate(roots):
 for b in roots[i+1:]:
  if any((a/p.name).exists() for p in b.glob('*.olean')): raise SystemExit(f'overlapping machine objects: {a} {b}')
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
out.mkdir();(out/'input-object-receipt.json').write_text(json.dumps([hashes(d) for d in roots],indent=2)+'\n')
print('Recorded input object hashes.',flush=True)
PY
export LEAN_PATH="$out:$roundtrip:$stage:$baseline:$project:$package:$lake_path"
for module in PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194ModelLoopIteration.modelIterZero PA194ModelLoopIteration.modelIterSucc PA194ModelLoopIteration.modelTimeZero PA194ModelLoopIteration.modelTimeSucc PA194ModelLoopIteration.modelIteration PA194ModelLoopState.modelNext PA194ModelLoopState.iterPacked PA194ModelLoopFrame.modelNested PA194ModelLoopFrame.modelWordCode PA194ModelLoopFrame.modelFrame; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$roundtrip" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
roots=list(map(Path,sys.argv[1:4]));expected=json.loads(Path(sys.argv[4]).read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if [hashes(d) for d in roots]!=expected: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194ModelLoopIteration.log" "$out/PA194ModelLoopState.log" "$out/PA194ModelLoopFrame.log"
echo 'Model-length exact-clock loop iteration schema checked.'
