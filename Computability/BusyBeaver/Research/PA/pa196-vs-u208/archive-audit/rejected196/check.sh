#!/usr/bin/env bash
set -eu
here=$(cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$here/check_inputs.py"
case "$(lean --version)" in
  *'version 4.32.0'*) ;;
  *) printf '%s\n' 'Lean 4.32.0 is required for this standalone check.' >&2; exit 1 ;;
esac
task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa196-rejected-XXXXXX")
trap 'rm -rf -- "$task_dir"' EXIT
cp -R "$here/Cert" "$task_dir/Cert"
cd "$task_dir"
export LEAN_PATH="$task_dir${LEAN_PATH:+:$LEAN_PATH}"
lean -o Cert/Common.olean Cert/Common.lean
lean -o Cert/Before.olean Cert/Before.lean
seq 0 17 | xargs -P "${PA196_REJECT_JOBS:-3}" -I '{}' sh -c \
  'lean -o "Cert/Batch$1.olean" "Cert/Batch$1.lean"' sh '{}'
lean Cert/Final.lean
