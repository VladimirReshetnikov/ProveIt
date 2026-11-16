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
  39ee862fb3dd391aff229bce7d7c52e0448c45be36bffafdc4d0f2a56a28f862 "$source_dir/PA194ActivePrefix.lean" \
  e80bebe51d09ff1f74b1205db992d82e050ce0aa2c26e5a0f5656add84ff48b4 "$source_dir/PA194CumulativeClock.lean" \
  d804c0fdbc8bd885d553665d8c0e3a671f0dc4db4001680f9223eb86b0c9b944 "$baseline/unified-coherent-manifest.json" \
  8b23b791247e4fb374ee0115773c59db0bd4eede5c3a14a4728758e3b6070778 "$baseline/PA194StepperCompose.olean" \
  7aa72b74a53bdc78cecc68fca7eee8192e6f556fe91c8cf4cadb899edadeb0d8 "$baseline/PA194Stepper.olean" | sha256sum -c -
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-conditional-model-length.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$baseline:$project:$package:$lake_path"
for m in PA194CumulativeClock PA194ActivePrefix; do
  cp "$source_dir/$m.lean" "$task_dir/$m.lean"
  lake env env LEAN_PATH="$LEAN_PATH" lean -R "$task_dir" -o "$task_dir/$m.olean" "$task_dir/$m.lean" 2>&1 | tee "$task_dir/$m.log"
  if rg -q 'sorryAx' "$task_dir/$m.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
done

for thm in clockZero clockSucc; do
  rg -q "^'PA194CumulativeClock\.$thm' depends on axioms:" "$task_dir/PA194CumulativeClock.log"
done
for thm in activeZero activeSucc activeContinues; do
  rg -q "^'PA194ActivePrefix\.$thm' depends on axioms:" "$task_dir/PA194ActivePrefix.log"
done
echo 'PASS: generic cumulative clock and active prefix checked against the staged coherent machine baseline.'
