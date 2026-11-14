#!/usr/bin/env python3
"""Replay an exact power-cover source recipe; no optimizer or solver is used.

The source-tree notation and closed-interval splice algorithm are adapted from
VladimirReshetnikov/ProveIt, candidate-k215/source_language.py and
k215-residual-parameter/vendor/source_splice.py. Those utilities in turn credit
the K225/K226 construction packet and Wade's MIT-0 register-machine framework.
This file preserves their tree semantics and checks the exact baseline/result
byte digests. It does not itself constitute a proof-assistant certificate.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def leaf(tree):
    return isinstance(tree[0], str)


def sites(tree, prefix=''):
    if leaf(tree):
        return [[prefix, *tree]]
    return sites(tree[0], prefix+'0') + sites(tree[1], prefix+'1')


def parse(rows):
    instructions = {path: (op, arg) for path, op, arg in rows}
    require(len(instructions) == len(rows), 'Duplicate instruction address')
    prefixes = {path[:i] for path in instructions for i in range(len(path))}
    require(not prefixes.intersection(instructions), 'Prefix overlaps instruction')
    require(all(p+b in prefixes or p+b in instructions
                for p in prefixes for b in '01'), 'Source is not a full binary tree')

    def visit(path):
        if path in instructions:
            op, arg = instructions[path]
            require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Bad primitive')
            return op, arg
        return visit(path+'0'), visit(path+'1')

    tree = visit('')
    require(sites(tree) == rows, 'Noncanonical source order')
    return tree


@cache
def size(tree):
    return 1 if leaf(tree) else size(tree[0])+size(tree[1])


@cache
def boundary(tree):
    if leaf(tree):
        op, arg = tree
        return (1 if op == 'CD' else arg if op == 'CB' else 0,
                arg if op == 'CC' else 0, op == 'CH')
    a, b = boundary(tree[0]), boundary(tree[1])
    return max(a[0]-1, b[0], 0), max(a[1], b[1]-1, 0), a[2] or b[2]


def serial(parts):
    require(bool(parts), 'An empty source fragment has no binary representation')
    return parts[0] if len(parts) == 1 else (parts[0], serial(parts[1:]))


def closed_forest(tree, lo, hi):
    result = []

    def visit(node, start=0):
        end = start+size(node)
        if end <= lo or hi <= start:
            return
        if lo <= start and end <= hi:
            require(boundary(node) == (0, 0, False), 'Macro is not closed')
            result.append(node)
            return
        require(not leaf(node), 'Partial primitive interval')
        visit(node[0], start)
        visit(node[1], start+size(node[0]))

    visit(tree)
    require(sum(map(size, result)) == hi-lo, 'Macro interval mismatch')
    return result


def splice(tree, lo, hi, replacement):
    replacements = 0

    def visit(node, start=0):
        nonlocal replacements
        end = start+size(node)
        if end <= lo or hi <= start:
            return node
        if lo <= start and end <= hi:
            require(boundary(node) == (0, 0, False), 'Removed factor is not closed')
            if start == lo:
                replacements += 1
                return replacement
            return None
        require(not leaf(node), 'Partial primitive replacement')
        a = visit(node[0], start)
        b = visit(node[1], start+size(node[0]))
        if a is None:
            if b is not None:
                require(boundary(b)[:2] == (0, 0), 'Open right remainder')
            return b
        if b is None:
            require(boundary(a)[:2] == (0, 0), 'Open left remainder')
            return a
        return a, b

    result = visit(tree)
    require(replacements == 1, 'Replacement was not inserted exactly once')
    return result


def metrics(tree):
    nodes = set()

    def visit(node):
        if node in nodes:
            return
        nodes.add(node)
        if not leaf(node):
            visit(node[0])
            visit(node[1])

    visit(tree)
    rows = sites(tree)
    return {'dag_nodes': len(nodes), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def build(baseline, recipe):
    raw = baseline.read_bytes()
    require(digest(raw) == recipe['baseline_sha256'], 'Baseline digest mismatch')
    original = parse(json.loads(raw))
    macros = {'m'+str(k): serial(closed_forest(original, *interval))
              for k, interval in recipe['macro_intervals'].items()}
    macros['next_c'] = macros['m168'], ('CI', 1)
    macros['two'] = macros['m177'], ('CI', 1)

    def decode(expr):
        if isinstance(expr, str):
            return macros[expr]
        if isinstance(expr, dict):
            require(set(expr) == {'primitive'}, 'Unknown recipe field')
            return tuple(expr['primitive'])
        require(isinstance(expr, list) and len(expr) == 2, 'Invalid recipe node')
        return decode(expr[0]), decode(expr[1])

    replacement = decode(recipe['replacement'])
    require(boundary(replacement) == (0, 0, False), 'Replacement is not closed')
    result = splice(original, *recipe['replace_interval'], replacement)
    require(boundary(result) == (0, 0, True), 'Invalid global source boundary')
    encoded = (json.dumps(sites(result), separators=(',', ':'))+'\n').encode('ascii')
    require(digest(encoded) == recipe['expected_source_sha256'], 'Result digest mismatch')
    require(metrics(result) == recipe['expected_metrics'], 'Source metric mismatch')
    return encoded


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=here.parent/'inputs/k215_sites.json')
    parser.add_argument('--recipe', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    recipe = json.loads(args.recipe.read_text())
    encoded = build(args.baseline, recipe)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(encoded)
    print(json.dumps({'status': 'EXACT_SOURCE_RECONSTRUCTION_PASS',
                      'sha256': digest(encoded), **recipe['expected_metrics']}, indent=2))


if __name__ == '__main__':
    main()
