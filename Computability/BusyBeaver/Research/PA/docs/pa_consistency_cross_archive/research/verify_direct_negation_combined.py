#!/usr/bin/env python3
"""Replay the frozen 197-state direct-negation/Combined construction.

The arithmetic N macro retains its clean-scratch precondition. This replay
checks primitive source simulation, not a new formal proof of that invariant
or of the PA consistency biconditional.
"""
from pathlib import Path
import hashlib
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Register the direct-negation macro before installing the Combined exterior.
import direct_diagonal_search as d
import combine_recent as x

P = Path(__file__).resolve().parent / 'direct_negation_combined'

def require(value, message):
    if not value:
        raise ValueError(message)

def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value

def main():
    require(__debug__, 'Run with assertions enabled.')
    tree = x.c.read_grammar(P / 'grammar.json')
    raw, index, shape = d.build(tree)
    folds = freeze(json.loads((P / 'folds.json').read_text()))
    rows, aliases = x.s.apply(raw, folds)
    require(rows == x.read_dense(P / 'machine.native.tm'), 'Native table differs')
    labels = json.loads((P / 'labels.json').read_text())
    require(len(labels) == len(set(labels)) == 198, 'Label count')
    require(labels[0] == 74 and labels[-1] == 254, 'Start/halt labels')
    dense = x.read_dense(P / 'machine.tm')
    require(set(dense) == {(q, b) for q in range(197) for b in (0, 1)}, 'Rows')
    require({(labels[q], b): (w, move, labels[n])
             for (q, b), (w, move, n) in dense.items()} == rows, 'Conjugacy')
    sites, instructions, cases = x.c.source(tree)
    require(freeze(sites) == freeze(json.loads((P / 'sites.json').read_text())),
            'Source sites differ')
    require(len(sites) == 3444 and len(cases) == 4472, 'Source census')
    runtime = x.c.validate(rows, cases)
    require(runtime['ok'] and runtime['contracts'] == 4472, 'Runtime')
    startup = x.startup(rows, sites)
    require(startup == {'ok': True, 'steps': 57922}, 'Startup')
    receipt = {'states': 197, 'source_sites': 3444, 'contracts': runtime,
               'startup': startup,
               'sha256': hashlib.sha256((P / 'machine.tm').read_bytes()).hexdigest()}
    require(receipt == json.loads((P / 'receipt.json').read_text()), 'Receipt differs')
    print(json.dumps({'status': 'PASS', **receipt}, indent=2))

if __name__ == '__main__':
    main()
