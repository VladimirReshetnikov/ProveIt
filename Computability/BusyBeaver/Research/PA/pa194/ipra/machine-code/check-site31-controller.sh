#!/usr/bin/env bash
set -euo pipefail
if (($# != 5)); then echo "usage: $0 REPO SOURCE FETCH_ROOT PROJECT_FOUNDATION PACKAGE_FOUNDATION" >&2; exit 2; fi
repo=$(realpath "$1")
source=$(realpath "$2")
fetch=$(realpath "$3")
project=$(realpath "$4")
package=$(realpath "$5")
for v in GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES; do
 if [[ -v "$v" ]]; then echo "Refusing inherited $v" >&2; exit 2; fi
done
check_inputs() {
 printf '%s  %s\n' \
  763a7fe17531d58211696a7f9f06034e8877f29ebdf0bd05c3e30ca8aaa22ed6 "$source/PA194SourceSite31Controller.lean" \
  22970fddb4704c19b7a1a2c76375cf2126f53b3cd362f5248ed0fd45ef941a02 "$fetch/source-closure.json" \
  f9ec6655194932e828e0b35c45ccb5c4b5e8abbe6e706c18418c96f417d8fb1d "$fetch/PA194SourceControllerStep.olean" \
  393e87b26bbfb10cf831f50fc595eb232f91cdf16f07a1906c7fab1eee27a4df "$fetch/PA194SourceRegisterRelation.olean" \
  32cb17640d91b18f7be3fd5ce49288fd1567218a38b22f11d92cd36e470c14fd "$fetch/PA194SourcePCBound.olean" \
  | sha256sum -c -
}
check_inputs
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-site31-controller.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
cp "$source/PA194SourceSite31Controller.lean" "$task_dir/PA194SourceSite31Controller.lean"
cd "$repo"
lake_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$task_dir:$fetch:$fetch/foundation-view:$project:$package:$lake_path"
lake env env LEAN_PATH="$LEAN_PATH" lean -M6000 -j1 -R "$task_dir" -o "$task_dir/PA194SourceSite31Controller.olean" "$task_dir/PA194SourceSite31Controller.lean" 2>&1 | tee "$task_dir/check.log"
if rg -q 'sorryAx' "$task_dir/check.log"; then echo 'Unexpected sorryAx' >&2; exit 1; fi
for spec in site31Instruction updateRegister0 updatedRegs controllerStep; do
 rg -q "^'PA194SourceSite31Controller\.$spec' depends on axioms:" "$task_dir/check.log"
done
check_inputs
echo 'PASS: site-31 controller step; fetch/foundation roots remain prebuilt.'
