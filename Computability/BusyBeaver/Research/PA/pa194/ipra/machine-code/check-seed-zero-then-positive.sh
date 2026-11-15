#!/usr/bin/env bash
set -euo pipefail
if (($# != 6)); then echo 'usage: REPO SITE27_BASELINE PROJECT PACKAGE COMPOSITION_SOURCE NEW_OUTPUT' >&2; exit 2; fi
repo=$(realpath "$1"); baseline=$(realpath "$2"); project=$(realpath "$3"); package=$(realpath "$4"); source=$(realpath "$5"); out=$(realpath -m "$6")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
[[ ! -e "$out" && ! -L "$out" && "$out/" != "$baseline/"* && "$baseline/" != "$out/"* ]] || { echo 'Existing output or baseline/output overlap' >&2; exit 2; }
printf '%s  %s\n' 6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" 19e21d3724252604606557d1434dd2fd717b2b3bdf3f779f019627c816696a12 "$source" | sha256sum -c -
cd "$repo"
source_dir=${PA194_COMPOSITION_SOURCE_DIR:-"$repo/Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code"}
source_dir=$(realpath "$source_dir")
check_sources() {
 printf '%s  %s\n' \
  4da56e9178bdb0950df59671d505fde659bb2f709aaecf0a108231bdfa18ba6a "$source_dir/PA194Site27PathStep.lean" \
  69044b06d8b83ad8562a76af549df11391d936ebfb87b9f0b1ba2963b7301ed0 "$source_dir/PA194Path25To27.lean" | sha256sum -c -
}
check_sources
seed_source="$(dirname "$source")/PA194SeedZeroThenPositive.lean"
check_seed() { printf '%s  %s\n' ffbbed3f044ce47eff45bd7c0f884bc3fd44ae567561c52d321e0be78abded87 "$seed_source" | sha256sum -c -; }
check_seed
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
for module in PA194Site27PathStep PA194Path25To27; do
 lean -M6000 -j1 -R "$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean" > "$out/$module.log" 2>&1
 if rg -q 'sorryAx' "$out/$module.log"; then echo "Unexpected sorryAx: $module" >&2; exit 1; fi
done
lean -M6000 -j1 -R "$(dirname "$source")" -o "$out/PA194ZeroThenPositive.olean" "$source" > "$out/lean.log" 2>&1
rg -q "'PA194Site27PathStep.zeroBranchPath27' depends on axioms:" "$out/PA194Site27PathStep.log"
rg -q "'PA194Path25To27.zeroBranchPath25To27' depends on axioms:" "$out/PA194Path25To27.log"
rg -q "'PA194ZeroThenPositive.zeroThenPositive' depends on axioms:" "$out/lean.log"
lean -M6000 -j1 -R "$(dirname "$seed_source")" -o "$out/PA194SeedZeroThenPositive.olean" "$seed_source" > "$out/seed.log" 2>&1
rg -q "'PA194SeedZeroThenPositive.seededZeroThenPositive' depends on axioms:" "$out/seed.log"
if rg -q 'sorryAx' "$out/seed.log"; then echo 'Unexpected sorryAx in seed theorem' >&2; exit 1; fi
if rg -q 'sorryAx' "$out/lean.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
printf '%s  %s\n' 19e21d3724252604606557d1434dd2fd717b2b3bdf3f779f019627c816696a12 "$source" | sha256sum -c -
check_sources
check_seed
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
cat "$out/lean.log" "$out/seed.log"
echo 'Site-25-to-site-28 composition and blank-tape seed specialization checked.'
