#!/usr/bin/env python3
"""Compare a literal table to the frozen current 194-state frontier.

Method follows the supplied QN6 exact-graph audit, with independent local
parsing. The deliberately enlarged equivalence includes arbitrary spanning
root, state renaming, reflection, bit complementation, and ignored actions
on terminal edges. This establishes graph difference, not a consistency
calibration or semantic inequivalence.
"""
import argparse
import hashlib
import json
from pathlib import Path

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        state, symbol, write, direction, target = line.split()
        state, symbol, write, target = map(int, (state, symbol, write, target))
        assert symbol in (0, 1) and write in (0, 1) and direction in ('L', 'R')
        assert (state, symbol) not in rows
        rows[state, symbol] = (write, direction, target)
    states = {s for s, b in rows}
    assert len(rows) == 2 * len(states) and states
    assert len({n for w, d, n in rows.values()} - states) == 1
    return rows, states

def canonical(rows, states):
    choices = []
    for complement in (0, 1):
        for reflection in (0, 1):
            for root in states:
                indices = {root: 0}
                queue = [root]
                word = []
                for state in queue:
                    for symbol in (0, 1):
                        write, direction, target = rows[state, symbol ^ complement]
                        if target not in states:
                            word.append((-1, -1, -1))
                        else:
                            if target not in indices:
                                indices[target] = len(queue)
                                queue.append(target)
                            word.append((write ^ complement, int(direction == 'R') ^ reflection, indices[target]))
                if len(queue) == len(states):
                    choices.append(tuple(word))
    assert choices, 'No root reaches every working control'
    return min(choices)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('candidate', type=Path)
    p.add_argument('--corpus', type=Path, default=Path(__file__).parent / 'current194_novelty_corpus.json')
    p.add_argument('--recompute', action='store_true', help='Independently regenerate every stored canonical tuple from its literal table')
    args = p.parse_args()
    assert __debug__, 'Assertions must be enabled'
    rows, states = read_table(args.candidate)
    key = canonical(rows, states)
    corpus = json.loads(args.corpus.read_text())
    comparisons, matches = 0, []
    for old in corpus['graphs']:
        if old['states'] != len(states):
            continue
        table_file = args.corpus.parent / old['file']
        assert hashlib.sha256(table_file.read_bytes()).hexdigest() == old['raw_sha256']
        word = tuple(tuple(x) for x in old['canonical_tuple'])
        assert hashlib.sha256(json.dumps(word, separators=(',', ':')).encode()).hexdigest() == old['canonical_sha256']
        if args.recompute:
            assert canonical(*read_table(table_file)) == word
        comparisons += 1
        if word == key:
            matches.append({'class':old['table_class'], 'source':old['source']})
    print(json.dumps({'revision':corpus['source_revision'], 'candidate':str(args.candidate),
        'states':len(states), 'rows':len(rows), 'comparisons':comparisons, 'matches':matches,
        'reference_tuple_regeneration':args.recompute,
        'raw_sha256':hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        'canonical_sha256':hashlib.sha256(json.dumps(key, separators=(',', ':')).encode()).hexdigest()}, indent=2))

if __name__ == '__main__':
    main()
