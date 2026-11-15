#!/usr/bin/env bash
set -euo pipefail
if (($# != 9)); then echo 'usage: REPO SITE27_BASELINE SITE28_STAGE ROUND_STAGE ROUNDTRIP_STAGE PROJECT PACKAGE SOURCE_DIR NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); stage=$(realpath "$3"); round=$(realpath "$4"); roundtrip=$(realpath "$5"); project=$(realpath "$6"); package=$(realpath "$7"); source_dir=$(realpath "$8"); out=$(realpath -m "$9")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" ]] || { echo 'Existing output' >&2; exit 2; }
for d in "$baseline" "$stage" "$round" "$roundtrip"; do
 [[ "$out/" != "$d/"* && "$d/" != "$out/"* ]] || { echo 'Overlapping output/input' >&2; exit 2; }
done
printf '%s  %s\n' \
 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
 49cc4be2b3dd41489bae271657feeb76a0b801c21c5a9e6425e9b4dadb5c6f06 "$stage/PA194Site28IncrementWrite.olean" \
 3b9735f9c08d9aaefcdb2ea6388911c89c9ae9452c64ae51c925fc58d9958eb8 "$round/PA194Site28BlankExit.olean" \
 62c58fdbd82a2e83b69e354779d430f3f5ab9204c588cc1f0ef2f071cb853afd "$roundtrip/PA194OneSpareIdentities.olean" | sha256sum -c -
check_sources() {
 printf '%s  %s\n' \
  88e92a9b07d46e57e210b45931e1daacba58685407a2f79dc17f17aae95c3fb1 "$source_dir/PA194Site28SeedTail.lean" \
  742c6800403d614749d4d531360df9bcc0980f4243cec66196f74a77ca6ba27b "$source_dir/PA194OneSpareSeed2.lean" \
  1bea488bcfe626c9377ddeffe564a278201297bef0d9cf9ec83f6aa06f5985d0 "$source_dir/PA194OneSpareSeed26.lean" \
  f60369042b0d6fdbf44ee192aeb27ffd58269c6c9e081639a4e78eccde4a12a8 "$source_dir/PA194SeedFileRoundTrip.lean" | sha256sum -c -
}
check_sources
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
python3 - "$baseline" "$stage" "$round" "$roundtrip" "$out" "$project:$package:$lake_path" <<'PY'
from pathlib import Path
import hashlib,json,sys
roots=list(map(Path,sys.argv[1:5]));out=Path(sys.argv[5])
for root in sys.argv[6].split(':'):
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
export LEAN_PATH="$out:$roundtrip:$round:$stage:$baseline:$project:$package:$lake_path"
for module in PA194Site28SeedTail PA194OneSpareSeed2 PA194OneSpareSeed26 PA194SeedFileRoundTrip; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
for report in PA194Site28SeedTail.natFileSeedTail PA194Site28SeedTail.modelFileSeedTail PA194OneSpareSeed2.fileRepeat PA194OneSpareSeed2.modelSeed PA194OneSpareSeed26.modelSeed26 PA194SeedFileRoundTrip.roundTrip; do
 module=${report%%.*}; rg -q "'$report' depends on axioms:" "$out/$module.log"
done
check_sources
python3 - "$baseline" "$stage" "$round" "$roundtrip" "$out/input-object-receipt.json" <<'PY'
from pathlib import Path
import hashlib,json,sys
roots=list(map(Path,sys.argv[1:5]));expected=json.loads(Path(sys.argv[5]).read_text())
def hashes(d): return {str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file() and p.suffix in ('.olean','.private','.server','.ir')}
if [hashes(d) for d in roots]!=expected: raise SystemExit('input objects changed during replay')
print('Verified unchanged input objects.',flush=True)
PY
cat "$out/PA194OneSpareSeed2.log" "$out/PA194OneSpareSeed26.log" "$out/PA194SeedFileRoundTrip.log"
echo 'One-valued-spare seed connection checked.'
