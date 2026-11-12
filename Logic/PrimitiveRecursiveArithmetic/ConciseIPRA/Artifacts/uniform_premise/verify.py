"""Replay fixed positive/negative proof data and the major-premise mutation.

This uses only Python's standard library. It does not execute historical corpus
code, assume correctness from the producer, or import either measured checker.
Pass an extracted package directory, or place this file at its root and omit it.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def check(script, packet, optimized):
    args = [sys.executable] + (['-O'] if optimized else []) + [str(script)]
    result = subprocess.run(args, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def verify(root):
    cases = json.loads((root / 'tests' / 'cases.json').read_text())
    programs = [root / 'code' / 'checker.py', root / 'code' / 'checker_compact.py']
    rows = []
    for program in programs:
        for optimized in (False, True):
            for case in cases:
                actual = check(program, case['packet'], optimized)
                rows.append({'program': program.name, 'optimized': optimized,
                             'case': case['name'], 'expected': case['accept'],
                             'actual': actual, 'pass': actual == case['accept']})
    attack = next(case for case in cases if case['name'] == 'scalar_false_sentinel_attack')
    mutants = []
    with tempfile.TemporaryDirectory(prefix='ipra_major_guard_') as folder:
        for program in programs:
            source = program.read_text()
            needle = '    c(m, g)\n'
            if source.count(needle) != 1:
                raise ValueError('Missing or ambiguous mutation target: ' + program.name)
            mutant = Path(folder) / program.name
            mutant.write_text(source.replace(needle, '', 1))
            for optimized in (False, True):
                actual = check(mutant, attack['packet'], optimized)
                mutants.append({'program': program.name, 'optimized': optimized,
                                'mutation': 'delete mandatory major-premise proof',
                                'false_conclusion': '1 = 0',
                                'mutant_accepts': actual, 'pass': actual})
    result = {
        'case_count': len(cases),
        'expected_accept_count': sum(c['accept'] for c in cases),
        'expected_reject_count': sum(not c['accept'] for c in cases),
        'ordinary_checks': len(rows), 'mutation_checks': len(mutants),
        'program_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in programs},
        'results': rows, 'mutations': mutants,
        'mismatches': sum(not r['pass'] for r in rows + mutants),
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', nargs='?', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--write', type=Path, help='Optional output JSON report')
    args = parser.parse_args()
    result = verify(args.root.resolve())
    if args.write:
        args.write.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                     if k not in ('results', 'mutations')}, indent=2))
    if result['mismatches']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
