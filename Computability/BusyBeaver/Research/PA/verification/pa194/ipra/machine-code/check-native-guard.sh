#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then
  echo "usage: $0 REPO SOURCE_DIR COHERENT_BASE PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
  exit 2
fi
repo=$(realpath "$1")
src=$(realpath "$2")
baseline=$(realpath "$3")
project=$(realpath "$4")
package=$(realpath "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  b26da9d1090467c7c7ef65145e5fa96f85ca68419d378786a26b941b7cc98611 "$src/PA194GuardModel.lean" \
  56c3d50fefc8fae94a5833014ec39752b4f7ad3724901aada1686576724bae1a "$src/PA194NativeGuard.lean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-native-guard.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
cp "$src/PA194GuardModel.lean" "$src/PA194NativeGuard.lean" "$task_dir/"
for m in PA194GuardModel PA194NativeGuard; do
  echo "Checking $m"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194GuardModel\.guardEqual' depends on axioms:" "$task_dir/PA194GuardModel.log"
rg -q "^'PA194NativeGuard\.nativeGuardedOfModels' depends on axioms:" "$task_dir/PA194NativeGuard.log"
echo 'PASS: both source files checked in one fresh output; coherent baseline and general foundation objects remain prebuilt.'
