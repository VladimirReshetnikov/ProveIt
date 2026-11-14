#!/usr/bin/env bash
set -euo pipefail
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
wrapper_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-model-header-coherent-wrapper.XXXXXXXX")
trap 'rm -rf "$wrapper_dir"' EXIT
python3 - "$base/check-dense-startup-coherent.sh" "$wrapper_dir/combined.sh" <<'PY'
from pathlib import Path
import sys
source=Path(sys.argv[1]).read_text()
marker='for m in PA194ModelDenseStartup PA194StartupSentence; do'
if source.count(marker)!=1:
    raise SystemExit('unexpected coherent startup checker structure')
extra=r'''
# All machine-specific dependencies are rebuilt into the same fresh output.
python3 "${PA194_HEADER_BUILDER:-$base/build-model-header-coherent.py}" --repo "$repo" --out "$task_dir" \
  --jobs "${PA194_HEADER_JOBS:-2}"
'''
Path(sys.argv[2]).write_text(source+'\n'+extra)
PY
bash -n "$wrapper_dir/combined.sh"
# This supplies only the repository path; it does not override Git internals.
export PA194_AUDIT_REPO_OVERRIDE="$repo"
bash "$wrapper_dir/combined.sh"
