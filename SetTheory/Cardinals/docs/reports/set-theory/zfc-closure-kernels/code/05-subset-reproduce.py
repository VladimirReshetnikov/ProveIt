#!/usr/bin/env python3
"""Reproduce the reference checks. Optional table input is never downloaded.

Usage: python reproduce.py [--table /path/to/pinned/zfc_254.tm]
The full PDF build is separate: python build.py
"""
from __future__ import annotations
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
from kernel import check, Imp, M, dump_formula
from codec import encode, index


def examples() -> None:
    a = M(0, 0)
    aa = Imp(a, a)
    atom, implication = dump_formula(a), dump_formula(aa)
    identity = [[0, atom, implication], [0, atom, atom],
                [1, atom, implication, atom], [5, 0, 2], [5, 1, 3]]
    samples = {
        'identity': identity,
        'congruence': [[7]],
        'subset-closure': [[8, [1, 0, 1]]],
        'rejected-bottom': [[0]],
    }
    out = {}
    for name, value in samples.items():
        (ROOT / 'examples' / (name + '.json')).write_text(
            json.dumps(value, indent=2) + '\n', encoding='utf-8')
        result = asdict(check(value))
        result['encoded_bits'] = len(encode(value))
        result['candidate_index_hex'] = hex(index(value))
        out[name] = result
    assert out['identity']['valid'] and not out['identity']['refutation']
    assert out['congruence']['valid'] and not out['congruence']['refutation']
    assert out['subset-closure']['valid'] and not out['subset-closure']['refutation']
    assert not out['rejected-bottom']['valid']
    (ROOT / 'results' / 'examples.json').write_text(
        json.dumps(out, indent=2) + '\n', encoding='utf-8')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path)
    parser.add_argument('--examples-only', action='store_true')
    args = parser.parse_args()
    (ROOT / 'results').mkdir(exist_ok=True)
    (ROOT / 'examples').mkdir(exist_ok=True)
    examples()
    if args.examples_only:
        print('Examples generated and checked; none is a refutation.')
        return
    run = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s',
                          str(ROOT / 'code'), '-v'], cwd=ROOT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (ROOT / 'results' / 'unit-tests.txt').write_text(run.stdout, encoding='utf-8')
    print(run.stdout)
    run.check_returncode()
    for script in ('metrics.py', 'experiments.py'):
        subprocess.run([sys.executable, str(ROOT / 'code' / script)], cwd=ROOT, check=True)
    if args.table is not None:
        subprocess.run([sys.executable, str(ROOT / 'code' / 'audit_tm.py'),
                        str(args.table.resolve()), '--output',
                        str(ROOT / 'results' / 'tm-audit.json')], check=True, cwd=ROOT)
    else:
        print('Pinned TM table audit NOT rerun: pass --table to reproduce it.\n'
              'The delivered results/tm-audit.json records the authoring-session audit.')
    print('Reference checks passed. No formal ZFC/PA proof or TM compilation is claimed.')


if __name__ == '__main__':
    main()
