#!/usr/bin/env bash
set -eu
here=$(cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$here/generate.py" --check
case "$(lean --version)" in
  *'version 4.32.0'*) ;;
  *) printf '%s\n' 'Lean 4.32.0 is required for this standalone check.' >&2; exit 1 ;;
esac
task_dir=$(mktemp -d "${TMPDIR:-/tmp}/pa196-conjugacy-XXXXXX")
trap 'rm -rf -- "$task_dir"' EXIT
cp -R "$here/NativeDense" "$task_dir/NativeDense"
cd "$task_dir"
export LEAN_PATH="$task_dir${LEAN_PATH:+:$LEAN_PATH}"
lean -o NativeDense/Core.olean NativeDense/Core.lean
lean NativeDense/Tables.lean
