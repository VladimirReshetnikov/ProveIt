#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then
  echo "usage: $0 REPO SOURCE_DIR UNIFIED_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
  exit 2
fi
repo=$(realpath "$1")
source=$(realpath "$2")
baseline=$(realpath "$3")
project=$(realpath "$4")
package=$(realpath "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  9054a253d607950b9946d04526ab40eceaac020a7e0690c7da12f0abbb520024 "$source/PA194SourceHaltSite.lean" \
  54ef8d68d165f2a2b98edff5662d86053d203091e4bbd19b1c4fe6b39949aa7e "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-source-tree/generate.py" \
  664befae8fdc26dc86ce229a4efb0da7210a5be89d9490b74d5e96c9be75e0ce "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-coverage/PA194SourceProgram.lean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-source-halt-site.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
python3 "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-source-tree/generate.py" "$task_dir/PA194SourceTree.lean"
printf '%s  %s\n' 69f6dee4807f25ed36923a86b87c20bc23432bdaf43bf8a41148f76f05540ca1 "$task_dir/PA194SourceTree.lean" | sha256sum -c -
python3 - "$repo" <<'PY'
import hashlib,sys
from pathlib import Path
root=Path(sys.argv[1]); sys.path.insert(0,str(root/'Computability/BusyBeaver/Research/PA'))
from packet_inputs import PlacedPacket
with PlacedPacket(root,'194') as p:
    b=p.read('pa194_conpa/construction/tables/pa194.tm')
assert hashlib.sha256(b).hexdigest()=='4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
print('Pinned literal table hash: OK (link to source semantics is a separate obligation)')
PY
cp "$repo/Computability/BusyBeaver/Research/PA/pa194-work/pa194-coverage/PA194SourceProgram.lean" "$task_dir/"
cp "$source/PA194SourceHaltSite.lean" "$task_dir/"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194SourceTree PA194SourceProgram PA194SourceHaltSite; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in haltSiteAt10 haltSiteResolves uniqueHaltLeaf; do
  rg -q "^'PA194SourceHaltSite.$thm' depends on axioms:" "$task_dir/PA194SourceHaltSite.log"
done
echo 'PASS: regenerated source tree and halt-site certificate checked; retained upstream foundation and machine overlays remain prebuilt.'
