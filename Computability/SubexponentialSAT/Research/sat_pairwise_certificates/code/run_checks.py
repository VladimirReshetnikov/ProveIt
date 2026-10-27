#!/usr/bin/env python3
"""Regenerate all new finite certificates; requires Python standard library."""
import json
from pathlib import Path
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parents[1]
    out = root / 'results'
    out.mkdir(exist_ok=True)
    summary = {'status': 'PASS', 'checks': []}
    for name in ('cached', 'streamed', 'rank_window'):
        script = root / 'code' / ('check_' + name + '.py')
        normal = subprocess.run([sys.executable, str(script)], check=True,
                                capture_output=True, text=True).stdout
        optimized = subprocess.run([sys.executable, '-O', str(script)], check=True,
                                   capture_output=True, text=True).stdout
        if normal != optimized:
            raise ValueError(name + ': normal and optimized outputs differ')
        json.loads(normal)
        (out / (name + '_checks.json')).write_text(normal, encoding='utf-8')
        summary['checks'].append({'name': name, 'normal_equals_optimized': True})
    cached = json.loads((out / 'cached_checks.json').read_text())
    streamed = json.loads((out / 'streamed_checks.json').read_text())
    summary['cached_eventual_coefficient'] = cached['schedule']['eventual_time_and_space_coefficient']
    summary['low_degree_ps_eventual_coefficient'] = streamed['low_degree']['eventual_safe_coefficient']
    summary['pair_support_choices'] = cached['certificate']['pairwise_support_choices_checked']
    (out / 'verification_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
