#!/usr/bin/env bash
# Reproduce the report's finite certificates; an upstream clone is optional.
# This script does not run Lean or fetch/install dependencies.
set -euo pipefail

if (( $# > 1 )); then
    printf 'Usage: bash code/reproduce.sh [/path/to/pinned/grh-lean]\n' >&2
    exit 2
fi

upstream_clone=''
if (( $# == 1 )); then
    upstream_clone="$(cd -- "$1" && pwd -P)"
fi
bundle_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd -- "$bundle_root"
python_bin="${GRH_REPORT_PYTHON:-python3}"

"$python_bin" - <<'PY'
import hashlib
from pathlib import Path
import sympy  # dependency check before replacing any generated data
manifest = Path('evidence/UPSTREAM_SHA256SUMS.txt')
entries = manifest.read_text().splitlines()
for entry in entries:
    digest, name = entry.split('  ', 1)
    actual = hashlib.sha256((manifest.parent / name).read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f'Upstream excerpt checksum mismatch: {name}')
print(f'Verified {len(entries)} unchanged upstream excerpt files.')
PY

run_json() {
    local script="$1" target="$2" temporary
    shift 2
    temporary="$(mktemp "${target}.tmp.XXXXXX")"
    if ! "$python_bin" "$script" "$@" > "$temporary"; then
        rm -f -- "$temporary"
        return 1
    fi
    if ! "$python_bin" -m json.tool "$temporary" > /dev/null; then
        rm -f -- "$temporary"
        return 1
    fi
    mv -- "$temporary" "$target"
    printf 'Reproduced %s\n' "$target"
}

run_json code/a5_detector.py data/a5_detector_results.json
run_json code/genus_certificate.py data/genus_certificate.json
run_json code/torsion_checks.py data/torsion_checks.json

"$python_bin" - <<'PY'
import csv
from fractions import Fraction
import json
from pathlib import Path
data = json.loads(Path('data/genus_certificate.json').read_text())
target = Path('data/genus_certificate.csv')
def rational(row):
    return str(Fraction(row['numerator'], row['denominator']))
with target.open('w', newline='') as stream:
    writer = csv.writer(stream)
    writer.writerow(['field_degree', 'safe_radius', 'a', 'b',
                     'endpoint_ratio_numerator', 'endpoint_ratio_denominator'])
    for row in data['certificates']:
        ratio = row['exact_ratio_to_census_cutoff']
        writer.writerow([row['field_degree'], row['safe_ramified_norm_radius'],
                         rational(row['a']), rational(row['b']),
                         ratio['numerator'], ratio['denominator']])
print(f'Reproduced {target}')
PY

if [[ -n "$upstream_clone" ]]; then
    run_json code/source_audit.py data/source_audit.json "$upstream_clone"
else
    printf 'Static inventory retained; supply the pinned full clone to rerun it.\n'
fi

if command -v latexmk > /dev/null 2>&1; then
    if [[ -f report.tex ]]; then
        latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
    else
        printf 'PDF build skipped: report.tex is not present.\n' >&2
    fi
else
    printf 'PDF build skipped: latexmk is not installed.\n'
fi

printf 'Finite certificate reproduction completed; no Lean build was run.\n'
