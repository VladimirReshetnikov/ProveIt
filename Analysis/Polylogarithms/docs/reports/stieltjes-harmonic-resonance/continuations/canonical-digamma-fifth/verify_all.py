#!/usr/bin/env python3
"""Replay exact identities; add --full for the slower numerical diagnostics."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import mpmath
import sympy

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    (ROOT / 'results').mkdir(exist_ok=True)
    commands = [
        ['code/verify_fifth.py'],
        ['code/verify_scalar.py', '--output', 'results/scalar_verification.json'],
        ['code/verify_gamma.py', '--exact-only', '--output', 'results/gamma_exact_verification.json'],
        ['code/verify_tail_rank.py', '--exact-only'],
    ]
    if args.full:
        commands.extend([
            ['code/numeric_fifth.py'],
            ['code/verify_gamma.py'],
            ['code/verify_tail_rank.py'],
            ['code/check_young_sign.py'],
        ])
    records = []
    for command in commands:
        print('Running ' + ' '.join(command), flush=True)
        done = subprocess.run([sys.executable] + command, cwd=ROOT)
        records.append({'command': command, 'exit_code': done.returncode})
        if done.returncode:
            raise SystemExit(done.returncode)
    def read(name):
        return json.loads((ROOT / 'results' / name).read_text())
    counts = {
        'fifth': read('fifth_exact_results.json')['exact_checks'],
        'scalar': read('scalar_verification.json')['check_count'],
        'gamma': read('gamma_exact_verification.json')['exact']['assertions'],
        'tail_rank': read('tail_rank_exact_verification.json')['exact']['assertions'],
    }
    summary = {'all_passed': True, 'full_numeric_replay': args.full,
               'exact_counts': counts, 'total_exact_assertions': sum(counts.values()),
               'versions': {'python': sys.version.split()[0], 'sympy': sympy.__version__,
                            'mpmath': mpmath.__version__}, 'commands': records,
               'interval_certificate': False}
    (ROOT / 'results' / 'replay_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
