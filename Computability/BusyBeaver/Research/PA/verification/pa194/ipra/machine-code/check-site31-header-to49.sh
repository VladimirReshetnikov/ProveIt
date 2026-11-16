#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo "usage: $0 REPO SITE27_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION SOURCE" >&2; exit 2; fi
repo=$(realpath "$1")
baseline=$(realpath "$2")
project=$(realpath "$3")
package=$(realpath "$4")
source=$(realpath "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_inputs() {
 printf '%s  %s\n' \
  6d34ca8f62b040c0c1c4b0a83c10370aaf28edb029e5e998274e187032e0b543 "$baseline/site27-coherent-manifest.json" \
  58493be34ff68b69f7cdb9cafa7eadffac307262f1c62824c55867719b5a07bf "$baseline/PA194Site27HeaderDispatch.olean" \
  cf9150dbbb719a01bff0c7193ede46e8e57a9ae2ea8e80317f4855416ab0cc15 "$baseline/PA194LeftRows.olean" \
  c4aef4576f072a828247a9d934260cce89302bf31bcfc0aa2d2f48963f4cbcd2 "$baseline/PA194Path27Header.olean" \
  95d26c326cac59eb185413d7f3c0da2f85e5de983d663e525f76160c9d200327 "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/PA194Path31Header.lean" \
  318640b93f57c641cc76baca6e0738519e17135a9557d3b5e705773eb4fde328 "$source/PA194Site31HeaderDispatch.lean" \
  1b35891a7f5f994f0f69f829653fb5204ae28423fbf9ed23f2c244ee28748948 "$source/PA194Site31HeaderTo49.lean" \
  | sha256sum -c -
}
check_inputs
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-site31-header.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194Path31Header PA194Site31HeaderDispatch PA194Site31HeaderTo49; do
 case "$m" in
  PA194Path31Header) cp "$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/$m.lean" "$task_dir/$m.lean" ;;
  *) cp "$source/$m.lean" "$task_dir/$m.lean" ;;
 esac
 echo "Checking $m"
 lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
 if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for spec in PA194Path31Header:path31 PA194Site31HeaderDispatch:row63one PA194Site31HeaderDispatch:row89zero PA194Site31HeaderDispatch:sevenSteps PA194Site31HeaderTo49:row46odd PA194Site31HeaderTo49:row65one PA194Site31HeaderTo49:path31Input PA194Site31HeaderTo49:to49; do
 module=${spec%%:*}; thm=${spec#*:}
 rg -q "^'$module\.$thm' depends on axioms:" "$task_dir/$module.log"
done
check_inputs
echo 'PASS: site-31 physical header to control 49; staged machine/foundation roots remain prebuilt.'
