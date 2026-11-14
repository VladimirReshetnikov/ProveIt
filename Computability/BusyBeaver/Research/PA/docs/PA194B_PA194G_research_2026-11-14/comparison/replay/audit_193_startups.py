#!/usr/bin/env python3
"""Replay blank starts of the 193-state runtime experiments.

The inconsistent coefficient-three calculus is excluded: its rejection is
logical, not a startup failure. Every other frozen 193-state graph is tried
from every working control. A RAY result has an exact finite prefix followed
by a constant-state outward scan through a provably blank half-line. A LIMIT
is explicitly inconclusive and is never reported as a nontermination proof.
The test detects no source frames and establishes no consistency equivalence.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
from literal_inventory import parse_table

HERE = Path(__file__).resolve().parent
EXCLUDED = '29a6054edbfa'


def run(data, start, limit):
    rows, states, halt = data
    ones = set()
    state, head = start, 0
    for step in range(limit + 1):
        if state == halt:
            return dict(start=start, outcome='HALT', steps=step, state=state, head=head)
        bit = int(head in ones)
        write, move, target = rows[state, bit]
        direction = 1 if move == 'R' else -1
        # All cells farther in the direction of travel are blank. Repeating
        # the same transition never reads a previously written cell.
        if bit == 0 and target == state and (
            not ones or (head > max(ones) if direction == 1 else head < min(ones))
        ):
            return dict(start=start, outcome='RAY', steps=step, state=state,
                        head=head, write=write, move=move, one_cells=sorted(ones))
        if step == limit:
            return dict(start=start, outcome='LIMIT', steps=step,
                        state=state, head=head, one_count=len(ones))
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
        state = target
    raise AssertionError('unreachable')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--frontier', type=Path, default=HERE / 'frontier_tables')
    ap.add_argument('--ledger', type=Path, default=HERE / 'frontier193.json')
    ap.add_argument('--manifest', type=Path, default=HERE / 'table_manifest.json')
    ap.add_argument('--steps', type=int, default=10000)
    ap.add_argument('--output', type=Path, default=Path.cwd() / 'startup193-replay.json')
    args = ap.parse_args()
    assert args.steps >= 0
    ledger = json.loads(args.ledger.read_text())
    manifest = {x['file']: x['sha256'] for x in json.loads(args.manifest.read_text())['tables']}
    classes, totals, excluded = [], collections.Counter(), []
    for item in ledger['classes']:
        graph = item['graph_hash']
        name = graph + '.tm'
        raw = (args.frontier / name).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == manifest[name], name
        data = parse_table(raw)
        assert data is not None and len(data[1]) == 193
        if graph.startswith(EXCLUDED):
            excluded.append(dict(graph_hash=graph, name=item['name'],
                                 reason='Logical coding collision; not a startup-rejection experiment.'))
            continue
        runs = [run(data, state, args.steps) for state in sorted(data[1])]
        counts = collections.Counter(x['outcome'] for x in runs)
        totals.update(counts)
        classes.append(dict(graph_hash=graph, name=item['name'], counts=dict(counts), runs=runs))
    result = dict(snapshot=ledger['snapshot'], classes_tested=len(classes),
                  step_bound=args.steps, totals=dict(totals), excluded=excluded,
                  scope=__doc__, classes=classes)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'classes'}, indent=2))


if __name__ == '__main__':
    main()
