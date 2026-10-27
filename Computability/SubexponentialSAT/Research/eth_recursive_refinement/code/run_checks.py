#!/usr/bin/env python3
"""Replay the bundle's finite exact checks; no network or external packages."""
from pathlib import Path
import contextlib
import hashlib
import io
import json
import sys

import pivot21_validation
import check_schedule
import verify_packing
import mode_counts


def captured_json(function):
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        function()
    return json.loads(output.getvalue())


def main():
    root = Path(__file__).resolve().parents[1]
    results = root/'results'
    results.mkdir(exist_ok=True)
    kernel = pivot21_validation.check()
    (results/'kernel_checks.json').write_text(json.dumps(kernel, indent=2)+'\n')
    print('Exact kernel checks passed.', flush=True)
    schedule = captured_json(check_schedule.main)
    (results/'schedule_checks.json').write_text(json.dumps(schedule, indent=2)+'\n')
    print('Exact schedule checks passed.', flush=True)
    packing = captured_json(verify_packing.main)
    print('Exact packing checks passed.', flush=True)
    inventories = captured_json(mode_counts.main)
    print('Abstract mode counts completed.', flush=True)
    summary = {
        'status': 'pass',
        'scope': 'Finite exact algebra and combinatorics; no full SAT implementation or benchmark.',
        'kernel': kernel,
        'schedule_identities': schedule['schedule_identities_checked'],
        'schedule_size_samples': len(schedule['selected_logarithmic_size_instances']),
        'packing': packing,
        'mode_inventories': inventories,
        'code_sha256': {
            str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((root/'code').glob('*.py'))
        },
    }
    target = results/('checks_optimized.json' if sys.flags.optimize else 'checks.json')
    target.write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
