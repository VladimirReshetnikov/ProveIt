#!/usr/bin/env python3
"""Compare the standalone compiler with two authenticated upstream functions.

Only the parsed compile_windows definitions are executed; no upstream import,
top-level statements, builder or historical test suite executes. The complete
functions contain finite arithmetic and data-structure construction only.
"""
import argparse
import ast
import hashlib
from itertools import product
import json
from pathlib import Path
from types import SimpleNamespace

import k215_constants as new

BASELINE_HASH = '011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0'
MODIFIED_HASH = 'd6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2'


def extract_function(path, expected):
    raw = Path(path).read_bytes().rstrip(b'\n')+b'\n'
    digest = hashlib.sha256(raw).hexdigest()
    new.require(digest == expected, 'upstream source hash mismatch: '+str(path))
    parsed = ast.parse(raw.decode())
    fun = next(node for node in parsed.body
               if isinstance(node, ast.FunctionDef) and node.name == 'compile_windows')
    return ast.Module(body=[fun], type_ignores=[])


def run(baseline, modified):
    fields = ('windows a A coeff mu padding m positions payload dummy anchors '
              'anchor_unit H T1 T2 L R radix_bits d DCpoly MFpoly').split()
    def compiled(*args):
        return SimpleNamespace(**dict(zip(fields, args)))
    def is_five_power(value):
        while value > 1 and value % 5 == 0:
            value //= 5
        return value == 1
    env = dict(product=product, Compiled=compiled,
               next_five_power=new.next_five_power, is_five_power=is_five_power,
               previous=SimpleNamespace(previous=SimpleNamespace(add_term=new.add_term)))
    exec(compile(extract_function(baseline, BASELINE_HASH), str(baseline), 'exec'), env)
    parent = SimpleNamespace(compile_windows=env['compile_windows'],
                             next_five_power=new.next_five_power)
    modified_env = dict(baseline=parent)
    exec(compile(extract_function(modified, MODIFIED_HASH), str(modified), 'exec'), modified_env)
    fixtures = [([(0,)*9, (1,)*9], 2),
                (list(product(range(2), repeat=9))[:3], 2),
                (list(product(range(2), repeat=9))[:100], 2),
                ([(0,)*9, (1,)*9, (2,)*9], 3)]
    records = []
    names = dict(a='alphabet_size', anchor_unit='M0', radix_bits='b',
                 MF_native_poly='MFpoly', unshifted_mass_bound='mass_bound',
                 high_degree='g')
    for windows, alphabet_size in fixtures:
        old = modified_env['compile_windows'](windows, alphabet_size)
        actual = new.compile_windows(windows, alphabet_size)
        tested = []
        attributes = fields + ['extra_dummy', 'MF_native_poly', 'unshifted_mass_bound',
                                'unit_mod5', 'high_correction', 'high_degree']
        for attribute in attributes:
            if attribute in ('R', 'MFpoly'):
                continue
            new.require(getattr(old, attribute) == actual[names.get(attribute, attribute)],
                        'sparse layout mismatch: '+attribute)
            tested.append(attribute)
        records.append(dict(windows=len(windows), alphabet=alphabet_size,
                            exact_attributes_compared=len(tested),
                            high_correction=old.high_correction))
    new.require({r['high_correction'] for r in records} == {0, 1}, 'compiler branches')
    return dict(status='PASS', source_commit=new.COMMIT,
                method='Only authenticated extracted compile_windows functions executed; no upstream module top-level executed.',
                canonical_source_sha256={Path(baseline).name: BASELINE_HASH,
                                         Path(modified).name: MODIFIED_HASH},
                cases=records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=Path(__file__).resolve().parent/'upstream/explore_fixed_raw_universal_76.py')
    parser.add_argument('--modified', type=Path, default=Path(__file__).resolve().parent/'upstream/complete75_half_binomial_compiler.py')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.baseline, args.modified)
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
