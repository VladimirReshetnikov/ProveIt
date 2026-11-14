#!/usr/bin/env python3
"""Exhaust the specified bounded two-cell history-fold family on a table.

Candidate controls have predecessor-cell histories zero and one respectively;
all their incoming actions must move right and write that history. We replace
each of the merged control's rows by one left move to an existing control,
allowing either initial written bit. The rest of each proof trace follows
unchanged literal rows, does not read exterior tape, and cannot re-enter the
merged control. Thus a discovered result has exact finite all-tape identities.
An empty result is only an obstruction for this explicitly bounded family.
"""
import argparse
from collections import defaultdict
from itertools import product
import json
from pathlib import Path
import hashlib, sys
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
sys.path.insert(0, str(PACKAGE / 'comparison'))
from graph_tools import parse


def search(path, bound=21):
    rows, states = parse(path)
    incoming = defaultdict(set)
    for (q, read), (write, right, target) in rows.items():
        incoming[target].add((write, right))
    # Native74 and dense0 may be actual starts; exclude both conservatively.
    left = [q for q in states if incoming[q] == {(0, 1)} and q not in (0, 74)]
    right = [q for q in states if incoming[q] == {(1, 1)} and q not in (0, 74)]
    found = []
    for a, b in product(left, right):
        options = []
        for bit in (0, 1):
            valid = []
            actions = {(w, 0, h) for w in (0, 1) for h in states - {a, b}}
            if rows[a, bit] == rows[b, bit]:
                actions.add(rows[a, bit])
            for act in actions:
                lengths, ok = [], True
                for old, hist in ((a, 0), (b, 1)):
                    w, d, t = rows[old, bit]
                    expected = (b if t == a else t, 1 if d else -1, hist, w)
                    tape, head, cur = {-1: hist, 0: bit}, 0, b
                    for k in range(1, bound + 1):
                        if k == 1:
                            wr, dr, target = act
                        else:
                            if head not in tape or cur in {a, b} or cur not in states:
                                ok = False
                                break
                            wr, dr, target = rows[cur, tape[head]]
                        tape[head] = wr
                        head += 1 if dr else -1
                        cur = b if target == a else target
                        if (cur, head, tape[-1], tape[0]) == expected:
                            break
                    else:
                        ok = False
                    if not ok:
                        break
                    lengths.append(k)
                if ok:
                    valid.append({'action': act, 'lengths': lengths})
            options.append(valid)
        if all(options):
            found.append({'removed': a, 'retained': b, 'options': options})
    try:
        label = str(Path(path).resolve().relative_to(PACKAGE))
    except ValueError:
        label = str(path)
    return {'table': label, 'table_sha256': hashlib.sha256(Path(path).read_bytes()).hexdigest(), 'working_states': len(states),
            'left_history_controls': len(left), 'right_history_controls': len(right),
            'pairs': len(left) * len(right), 'trace_bound': bound,
            'initial_written_bit': 'both choices',
            'scope': __doc__, 'found': found}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table', type=Path)
    ap.add_argument('--receipt', type=Path, required=True)
    ap.add_argument('--bound', type=int, default=21)
    args = ap.parse_args()
    result = search(args.table, args.bound)
    args.receipt.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
