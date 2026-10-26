#!/usr/bin/env bash
set -euo pipefail
packet_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
proveit_dir="${1:?Usage: replay_checks.sh /absolute/path/to/ProveIt}"
cd "$proveit_dir"
python3 - <<'PYCHECK'
from pathlib import Path
import json
assert Path('lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.0', 'Wrong Lean toolchain'
manifest=json.loads(Path('lake-manifest.json').read_text())
mathlib=next(x for x in manifest['packages'] if x['name']=='mathlib')
assert mathlib['rev']=='81a5d257c8e410db227a6665ed08f64fea08e997', 'Wrong Mathlib revision'
PYCHECK
mkdir -p "$packet_dir/replay-logs"
for source_file in   lean/pell/ThirteenFreshSeedAudit.lean   lean/pell/SignedPellResidueAudit.lean   lean/canonical/CanonicalResidue.lean   lean/canonical/CanonicalDecoder.lean
do
  log_file="$packet_dir/replay-logs/$(basename "$source_file").log"
  printf 'Checking %s\n' "$source_file"
  if lake env lean "$packet_dir/$source_file" >"$log_file" 2>&1; then
    cat "$log_file"
  else
    cat "$log_file"
    exit 1
  fi
done
