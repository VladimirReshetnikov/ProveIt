#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then
  echo "usage: $0 REPO OUTPUT_SPEC_SOURCE UNIFIED_BASELINE PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2
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
  0a6440d6d5faada4bc5983a58e1a54bc3fcb16f3518339d5b7cd6e7679a469ae "$source" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  3068fd05bcff49f841bfcea607ae64bf929e5d369d20a0951e07a49a3b7eda26 "$baseline/PA194UnifiedSourceStepSentence.olean" \
  e90ef513043a92fca807f0d0255f3a8b1fa013d743351934b646fa92fe29057a "$baseline/PA194SelectedInputFile.olean" \
  c4aef4576f072a828247a9d934260cce89302bf31bcfc0aa2d2f48963f4cbcd2 "$baseline/PA194Path27Header.olean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-unified-output-spec.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
cp "$source" "$task_dir/PA194UnifiedOutputSpec.lean"
lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/PA194UnifiedOutputSpec.olean" "$task_dir/PA194UnifiedOutputSpec.lean" 2>&1 | tee "$task_dir/audit.log"
if rg -q 'sorryAx' "$task_dir/audit.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
for thm in zeroOutputWord zeroOutput positiveOutput selectedOutput; do
  rg -q "^'PA194UnifiedOutputSpec\.$thm' depends on axioms:" "$task_dir/audit.log"
done
echo 'PASS: output specification source checked against the staged coherent machine baseline.'
