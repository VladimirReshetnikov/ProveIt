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
  0a6440d6d5faada4bc5983a58e1a54bc3fcb16f3518339d5b7cd6e7679a469ae "$source_dir/PA194UnifiedOutputSpec.lean" \
  a49bc33ead8aab9b54e894eda1352061076acd9ee1ca0f83038a7077de1c6768 "$source_dir/PA194OpenFormulaTransfer.lean" \
  5bd111615bc4ca01a3ffd20e0bf24ec5949dca81f0b6ef7a0d4247af67173dde "$source_dir/PA194ZeroBranchImplication.lean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  3068fd05bcff49f841bfcea607ae64bf929e5d369d20a0951e07a49a3b7eda26 "$baseline/PA194UnifiedSourceStepSentence.olean" \
  e90ef513043a92fca807f0d0255f3a8b1fa013d743351934b646fa92fe29057a "$baseline/PA194SelectedInputFile.olean" \
  c4aef4576f072a828247a9d934260cce89302bf31bcfc0aa2d2f48963f4cbcd2 "$baseline/PA194Path27Header.olean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-unified-output-spec.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194UnifiedOutputSpec PA194OpenFormulaTransfer PA194ZeroBranchImplication; do
  cp "$source_dir/$m.lean" "$task_dir/$m.lean"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done
for thm in zeroOutputWord zeroOutput positiveOutput selectedOutput; do
  rg -q "^'PA194UnifiedOutputSpec\.$thm' depends on axioms:" "$task_dir/PA194UnifiedOutputSpec.log"
done
rg -q "^'PA194OpenFormulaTransfer\.nativeOpenOfClassical' depends on axioms:" "$task_dir/PA194OpenFormulaTransfer.log"
for thm in modelSentence classicalPRA nativeDisjunction nativeImplication; do
  rg -q "^'PA194ZeroBranchImplication\.$thm' depends on axioms:" "$task_dir/PA194ZeroBranchImplication.log"
done
echo 'PASS: three source modules checked in one fresh output against the staged coherent machine baseline.'
