#!/usr/bin/env bash
set -euo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo"
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-parent-zip.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
mkdir -p "$task_dir/M6"
export LEAN_PATH="$task_dir:$(lake env printenv LEAN_PATH)"
base=Computability/BusyBeaver/Research/PA
lean -M6000 -j1 -o "$task_dir/M6/Zip.olean" "$base/jamesyc-upstream/pa196/M6/Zip.lean"
for pair in 'pa194-quotient PA194LocalQuotient' 'pa194-all-tape PA194AllTape' 'pa194-control PA194ControlData' 'pa194-control PA194Control' 'pa195-generic-trace PA195GenericTrace' 'pa194-zip-bridge PA194ZipBridge'; do
  read -r dir mod <<< "$pair"
  lean -M6000 -j1 -o "$task_dir/$mod.olean" "$base/$dir/$mod.lean"
done
lean -M6000 -j1 "$base/pa194-parent-zip/PA194ParentZip.lean" | tee "$task_dir/axioms.log"
if rg -q 'sorryAx' "$task_dir/axioms.log"; then exit 1; fi
