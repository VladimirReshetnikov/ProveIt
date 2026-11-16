#!/usr/bin/env bash
set -euo pipefail
if (($# != 7)); then
  echo "usage: $0 REPO FRAME_SOURCE SELECTED_SOURCE PATH25_SOURCE COHERENT_BASE PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
  exit 2
fi
repo=$(realpath "$1")
frame=$(realpath "$2")
selected=$(realpath "$3")
path25=$(realpath "$4")
baseline=$(realpath "$5")
project=$(realpath "$6")
package=$(realpath "$7")
base="$repo/Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code"
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  5da81c6be780d630c30c9f4e2daedc9bd485febf49c192d877f32f5475e1db19 "$base/PA194ZeroOutputFile.lean" \
  2d359448873ffcc96f347826dd511e5bf589cbe55454b56f324a8d33349f7ddd "$base/PA194Path27Header.lean" \
  61e768ee58c34f1d14942ab521a2d6eabacb2a1c231141c1356d3c9794b24fb9 "$frame" \
  1d36207c6cee69ef00453695b6c57e780d305dda2fdbc4f495aa70de759a2642 "$selected" \
  5fe2df80831c2d4ce6fefee984438cacc7f00cd4e93d6ef343252e103dedfb2d "$path25" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-path27-frame.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
cp "$base/PA194ZeroOutputFile.lean" "$base/PA194Path27Header.lean" "$frame" "$selected" "$path25" "$task_dir/"
for m in PA194ZeroOutputFile PA194Path27Header PA194Path27Frame PA194SelectedFile PA194Path25Input; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in frame_bits_general path25 frame25_bits frame27_bits; do
  rg -q "^'PA194Path27Frame\.$thm' depends on axioms:" "$task_dir/PA194Path27Frame.log"
done
for thm in path27Word zeroResultIsPath27; do
  rg -q "^'PA194Path27Header\.$thm' depends on axioms:" "$task_dir/PA194Path27Header.log"
done
for thm in sourceFileSelected bitsEqWord frameSelectedBlank; do
  rg -q "^'PA194Path27Frame\.$thm' depends on axioms:" "$task_dir/PA194SelectedFile.log"
done
rg -q "^'PA194Path25Input\.site25Input' depends on axioms:" "$task_dir/PA194Path25Input.log"
echo 'PASS: all five source files checked in one fresh output; foundational and coherent baseline objects remain prebuilt.'
