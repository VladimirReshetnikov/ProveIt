#!/usr/bin/env python3
"""Diagnostic for the explicit infinite FC15 Eq-predicate model without E transport.

The universal proof is in fc15_without_e_countermodel.tex. This program
evaluates the immutable native/completion ASTs on a finite set of input
assignments; the carrier and all intermediate arithmetic remain infinite.
It is not a finite model checker, a ZFC consistency proof, or a TM compiler.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys
from types import ModuleType

HERE = Path(__file__).resolve().parent
REFERENCE_HASHES = {
    'ground_kernel.py': '2ceebc265a6d2dc5d487f4b9d078a53d6b37d7718184e6f2c6da920b6a4985fb',
    'coded_extensional.py': '57d8f48de761b2a0ce0cd29f63935b729da84e5e185a263fff331eba7f5d74f8',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


@contextmanager
def load_reference(path):
    names = ('ground_kernel', 'coded_extensional')
    previous = {name: sys.modules.get(name) for name in names}
    modules = []
    try:
        for name in names:
            file = path / (name + '.py')
            require(hashlib.sha256(file.read_bytes()).hexdigest() == REFERENCE_HASHES[file.name],
                    'Immutable reference digest changed: ' + file.name)
            module = ModuleType(name)
            module.__file__ = str(file)
            sys.modules[name] = module
            exec(compile(file.read_text(), str(file), 'exec'), module.__dict__)
            modules.append(module)
        yield tuple(modules)
    finally:
        for name, old in previous.items():
            if old is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = old


@lru_cache(maxsize=None)
def prime(index):
    require(index >= 0, 'Negative prime index')
    found = -1
    n = 2
    while True:
        if all(n % d for d in range(2, isqrt(n) + 1)):
            found += 1
            if found == index:
                return n
        n += 1


@lru_cache(maxsize=None)
def v(s, j):
    p, n, exponent = prime(j), s + 1, 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


@lru_cache(maxsize=None)
def c(s, j, z):
    p = prime(j)
    return ((s + 1) // p ** v(s, j)) * p ** z - 1


@lru_cache(maxsize=None)
def function(name, args):
    if name == 'd':
        return (0, 0)
    first = tuple(a[0] for a in args)
    if name == 'V':
        return (v(*first), 0)
    if name == 'C':
        return (c(*first), 0)
    if name == 'N':
        return (1 - (first[0] % 2) * (first[1] % 2), 0)
    if name in ('A', 'H'):
        return (0, 0)
    if name == 'Q':
        return (first[1], 0)
    if name == 'W':
        return (0, 1)
    if name in ('Y', 'Z'):
        return (first[2] + 1, 1)
    raise ValueError('Unknown native function: ' + name)


def term(tree, env):
    if isinstance(tree, str):
        return env[tree]
    return function(tree[0], tuple(term(t, env) for t in tree[1:]))


def predicate(name, a, b):
    if name == 'Eq':
        return a[0] == b[0]
    if name == 'E':
        return a[1] == b[1] == 1 and a[0] == b[0]
    if name == 'Inc':
        return b[0] % 2 == 1
    if name == 'G':
        return b[0] % 2 == 0
    raise ValueError('Unknown native predicate: ' + name)


def literal(lit, env):
    sign, pred, a, b = lit
    return predicate(pred, term(a, env), term(b, env)) == sign


def clause(row, env):
    return any(literal(lit, env) for lit in row)


def run(reference, first_bound):
    require(first_bound >= 3, 'Include the three first coordinates used by the exact fixtures')
    sample = tuple(product(range(first_bound), (0, 1)))
    with load_reference(reference) as (K, C):
        functions = K.signature(False, True)
        require(len(functions) == 9, 'Expected the exact derived-member signature')
        native = K.source_clauses(False, True)
        completion = K.equality_clauses(False, functions)
        e_rows = [row for row in completion if any(pred == 'E' for _, pred, *_ in row)]
        require(len(e_rows) == 1, 'Expected exactly one E-transport row')
        retained = [row for row in completion if row not in e_rows]
        require(len(native) == 15 and len(retained) == 13, 'Unexpected exact row count')
        checked = []
        for family, rows in (('native', native), ('completion_without_E', retained)):
            for i, row in enumerate(rows):
                variables = K.clause_variables(row)
                count = 0
                for values in product(sample, repeat=len(variables)):
                    env = dict(zip(variables, values))
                    require(clause(row, env), 'False ' + family + ' row ' + str(i + 1) + ': ' + str(env))
                    count += 1
                checked.append({'family': family, 'row': i + 1, 'variables': variables,
                                'assignments_checked': count, 'status': 'PASS'})

        # Both counterinstances use actual ground terms of the immutable signature.
        d, q = K.d, K.q
        w = K.f('W', d, d, d)
        ground_e = e_rows[0]
        env_e = {'x0': term(w, {}), 'x1': term(w, {}),
                 'y0': term(d, {}), 'y1': term(d, {})}
        e_values = [literal(lit, env_e) for lit in ground_e]
        require(e_values == [False] * 4, 'Ground E-transport fixture did not fail in every literal')
        j = K.f('C', d, q, q)
        env_ext = {'j': term(j, {}), 'a': term(d, {}), 'b': term(q, {})}
        require(env_ext == {'j': (2, 0), 'a': (0, 0), 'b': (1, 0)},
                'Unexpected explicit selector values')
        ext_values = [literal(lit, env_ext) for lit in C.extensional_clause()]
        require(ext_values == [False] * 4, 'FC16 failure fixture did not fail in every literal')

        return {
            'status': 'PASS',
            'scope': 'Finite input diagnostics for an explicit infinite model; universal proof is in the companion TeX.',
            'theory': 'FC15 native templates with Eq as a predicate, plus all original completion except E transport',
            'source_repository_commit': '6446ff5668307a2ac6aee1896037f0b792090389',
            'reference_sha256': REFERENCE_HASHES,
            'sample_first_coordinates': list(range(first_bound)),
            'sample_decorations': [0, 1],
            'sample_is_a_finite_carrier': False,
            'native_rows': 15,
            'retained_completion_rows': 13,
            'function_congruences_retained': functions,
            'total_assignments_checked': sum(row['assignments_checked'] for row in checked),
            'checked_rows': checked,
            'ground_E_failure': {'w': w, 'w_value': term(w, {}), 'd_value': term(d, {}),
                                 'literal_truth_values': e_values},
            'FC16_failure': {'selector': j, 'environment': env_ext,
                             'literal_truth_values': ext_values},
            'limitations': ['Eq is not genuine equality in this model.',
                            'The extra FC16 coded-extensionality clause fails.',
                            'Diagnostics do not replace the universal mathematical proof.'],
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, default=HERE.parent / 'theory_work' / 'reference')
    parser.add_argument('--first-bound', type=int, default=3)
    parser.add_argument('--output', type=Path, default=HERE / 'fc15_without_e_countermodel.json')
    args = parser.parse_args()
    result = run(args.reference, args.first_bound)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'rows': len(result['checked_rows']),
                      'assignments_checked': result['total_assignments_checked'],
                      'ground_E_transport_fails': True, 'FC16_added_row_fails': True,
                      'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
