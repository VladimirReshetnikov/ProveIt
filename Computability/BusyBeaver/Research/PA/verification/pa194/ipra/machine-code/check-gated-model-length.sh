#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then
  echo "usage: $0 REPO SOURCE_DIR UNIFIED_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
  exit 2
fi
repo=$(realpath "$1")
source_dir=$(realpath "$2")
baseline=$(realpath "$3")
project=$(realpath "$4")
package=$(realpath "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
  if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
printf '%s  %s\n' \
  9a7d34bcc9d3fe5f98a40c36bbd3e9d8eef3a1eb029abbea483fa69efcf56872 "$source_dir/PA194ConditionalModelLength.lean" \
  a935c16e162b720eefe71027118fb958aa7652c4475dc7103c9e7dceb7bf1dad "$source_dir/PA194GatedModelLength.lean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  8b23b791247e4fb374ee0115773c59db0bd4eede5c3a14a4728758e3b6070778 "$baseline/PA194StepperCompose.olean" \
  7aa72b74a53bdc78cecc68fca7eee8192e6f556fe91c8cf4cadb899edadeb0d8 "$baseline/PA194Stepper.olean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-conditional-model-length.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194ConditionalModelLength PA194GatedModelLength; do
  cp "$source_dir/$m.lean" "$task_dir/$m.lean"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
rg -q "^'PA194ConditionalModelLength\.simulateModelLength' depends on axioms:" "$task_dir/PA194ConditionalModelLength.log"
for thm in simulateBeforeHalt haltToSourceHit sourceHitToHalt; do
  rg -q "^'PA194GatedModelLength\.$thm' depends on axioms:" "$task_dir/PA194GatedModelLength.log"
done
echo 'PASS: gated conditional model-length framework checked against the staged coherent machine baseline.'
