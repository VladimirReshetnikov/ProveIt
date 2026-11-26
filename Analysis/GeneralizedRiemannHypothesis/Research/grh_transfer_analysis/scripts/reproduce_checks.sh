#!/usr/bin/env bash
# Reproduce finite arithmetic checks, with an optional pinned source audit.
# This script does not install dependencies or build the upstream GRH project.
set -euo pipefail

if (( $# > 1 )); then
  printf 'Usage: bash %s [absolute/path/to/grh-lean]\n' "$0" >&2
  exit 2
fi

package_root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
mkdir -p "$package_root/data" "$package_root/evidence"

python3 "$package_root/scripts/arithmetic_checks.py" \
  --output "$package_root/data/arithmetic_checks.json" \
  | tee "$package_root/evidence/arithmetic_checks.log"

python3 "$package_root/scripts/nonresidue_checks.py" \
  > "$package_root/data/nonresidue_checks.json"
python3 - "$package_root/data/nonresidue_checks.json" <<'PY'
import json
import sys
from pathlib import Path
path = Path(sys.argv[1])
result = json.loads(path.read_text(encoding="utf-8"))
print(f"PASS: exact least-nonresidue check for {result['prime_count']} primes.")
print(f"JSON output: {path}")
PY

if (( $# == 1 )); then
  repository_path=$1
  expected_commit=72fead102f663d5c7a407964a13dc0cf9d977207
  actual_commit=$(git -C "$repository_path" rev-parse HEAD)
  if [[ "$actual_commit" != "$expected_commit" ]]; then
    printf 'Static audit stopped: expected commit %s, found %s.\n' \
      "$expected_commit" "$actual_commit" >&2
    exit 1
  fi
  python3 "$package_root/scripts/static_audit.py" "$repository_path" \
    > "$package_root/data/static_audit.json"
  printf 'Static lexical/import audit completed; no Lean proof-kernel replay performed.\n'
  printf 'JSON output: %s/data/static_audit.json\n' "$package_root"
fi

printf 'Finite checks completed. Supplemental checks alone do not prove GRH.\n'
