#!/usr/bin/env bash
set -euo pipefail
repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}
cd "$repo"
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
task_dir=$(mktemp -d "${TMPDIR:-/dev/shm}/pa194-seed-header-wrapper.XXXXXXXX")
trap 'rm -rf "$task_dir"' EXIT
python3 - "$base/check-startup-source-frame.sh" "$task_dir/prerequisites.sh" <<'PY'
from pathlib import Path
import sys
s = Path(sys.argv[1]).read_text()
old_repo = 'repo=${PA194_REPO_ROOT:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)}'
new_repo = 'repo=$(git rev-parse --show-toplevel)'
old = 'for name in firstSeedSourceStep seedArgs_logical modelSourceSeed seedRight_sourceLayout modelDenseStartupSourceFrame; do'
new = r'''printf '%s  %s\n' \
  68b6e0738e937dd5ed400d91e8896a928fb8354627a232a20a80d85181b794b5 "$PA194_PROJECT_OVERLAY/PA194IncrementDispatch.olean" \
  2d6952347e4db6908821df543aafdb4058ce11466987da8672d227daf6790bda "$PA194_PROJECT_OVERLAY/PA194LeftRows.olean" \
  44d5084d89663bb5b60f7e2615a1d471de0353bab10739be5aa468ce3c7683eb "$base/PA194IncrementDispatch.lean" \
  9f5f619fd5af9ecf205b1cf886b75618d98b99903f153a5765ecf7b309738e20 "$base/PA194LeftRows.lean" | sha256sum -c
header_source=${PA194_SEED_HEADER_SOURCE:-$base/PA194SeedHeaderDispatch.lean}
header_source=$(realpath "$header_source")
lake env env LEAN_PATH="$lean_path" lean -R "$(dirname "$header_source")" -M6000 -j1 \
  -o "$task_dir/PA194SeedHeaderDispatch.olean" "$header_source" | tee -a "$task_dir/axioms.log"
for theorem in PA194SeedHeaderDispatch.modelSeedAt84 PA194SeedHeaderDispatch.twelveSteps; do
  rg -q "'$theorem' depends on axioms:" "$task_dir/axioms.log"
done
''' + old
if s.count(old_repo) != 1 or s.count(old) != 1:
    raise SystemExit('unexpected startup source-frame checker structure')
Path(sys.argv[2]).write_text(s.replace(old_repo, new_repo, 1).replace(old, new, 1))
PY
bash -n "$task_dir/prerequisites.sh"
bash "$task_dir/prerequisites.sh"
