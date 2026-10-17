#!/usr/bin/env python3
"""Regenerate generic constructor metrics from the pinned C254 term ASTs.

Parameters and the distinguished falsity constant F are leaves. Constructors
are counted after expanding wn, wa, wex and named fixed definitions. Repeated
subterms count repeatedly in occurrences, but once in distinct_constructor_terms.
These syntactic counts do not count literal decoding, normalization, registers,
Python operations or Turing-machine states. Uses the Python standard library.
"""
import argparse
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
PRIMITIVES = {'wim': 0, 'wel': 1, 'wal': 2, 'weq': 3}
NAMES = ['rho1', 'rho2', 'rho3', 'rho4', 'rho5', 'rho6', 'rho7', 'rho8',
         'bundleC', 'bundleG', 'bundle']
F = ('leaf', 'F')


def metrics(spec):
    definitions = spec['definitions']
    if set(definitions) != set(NAMES):
        raise ValueError('Unexpected fixed-definition set')

    def apply(name, args, stack):
        if name in PRIMITIVES:
            if len(args) != 2:
                raise ValueError('Binary constructor arity')
            return ('b', PRIMITIVES[name], *args)
        if name == 'wn':
            if len(args) != 1:
                raise ValueError('Negation arity')
            return ('b', 0, args[0], F)
        if name in ('wa', 'wex'):
            if len(args) != 2:
                raise ValueError('Derived binary constructor arity')
            inner = apply('wn', [args[1]], stack)
            middle = apply('wim' if name == 'wa' else 'wal',
                           [args[0], inner], stack)
            return apply('wn', [middle], stack)
        if name in stack:
            raise ValueError('Cyclic fixed definition')
        item = definitions[name]
        env = dict(zip(item['parameters'], args, strict=True))

        def expand(term):
            if type(term) is str:
                return F if term == 'F' else env[term]
            if type(term) is int:
                return ('leaf', term)
            if type(term) is not list or not term:
                raise ValueError('Malformed fixed term')
            return apply(term[0], [expand(t) for t in term[1:]], stack + (name,))

        return expand(item['term'])

    result = {}
    for name in NAMES:
        args = [('leaf', p) for p in definitions[name]['parameters']]
        term = apply(name, args, ())
        distinct = set()

        def visit(node):
            if node[0] == 'leaf':
                return 0, 0
            distinct.add(node)
            left, right = visit(node[2]), visit(node[3])
            return 1 + left[0] + right[0], 1 + max(left[1], right[1])

        count, depth = visit(term)
        result[name] = {'constructor_occurrences': count, 'depth': depth,
                        'distinct_constructor_terms': len(distinct)}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=Path, default=BASE/'data/spec254.json')
    parser.add_argument('--output', type=Path, default=BASE/'data/schema_metrics.json')
    parser.add_argument('--check', action='store_true',
                        help='Compare with the saved JSON without rewriting it')
    args = parser.parse_args()
    source = args.spec.read_bytes()
    generated = metrics(json.loads(source))
    if args.output.exists():
        if json.loads(args.output.read_text()) != generated:
            raise SystemExit('FAIL: regenerated metrics differ from ' + str(args.output))
    elif args.check:
        raise SystemExit('FAIL: saved metrics do not exist: ' + str(args.output))
    if not args.check:
        args.output.write_text(json.dumps(generated, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'definitions_checked': len(generated),
                      'spec_sha256': hashlib.sha256(source).hexdigest(),
                      'mode': 'check' if args.check else 'regenerate',
                      'metrics': generated}, indent=2))


if __name__ == '__main__':
    main()
