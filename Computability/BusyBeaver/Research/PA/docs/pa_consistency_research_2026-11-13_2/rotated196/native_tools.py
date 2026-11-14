#!/usr/bin/env python3
"""Native table and decoder utilities extracted from ProveIt build221.py.
Attribution is retained in ../licenses/. This copy omits its K221 builder.
"""
from pathlib import Path
from collections import defaultdict
import argparse,json,hashlib,sys
import source_language as s
HERE=Path(__file__).resolve().parent
HALT=254
def need(x,m):
 if not x:raise ValueError(m)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def read_table(raw):
    rows = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need((q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad table row')
        rows[q, b] = (w, 1 if d == 'R' else -1, target)
    need(starts == [74], 'Expected PA196 native start74')
    states = {q for q, b in rows}
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Partial table')
    need({t for w, d, t in rows.values()} - states == {HALT}, 'Unexpected terminal state')
    return rows


def table_bytes(rows, start=74):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {target}\n'
        for (q, b), (w, d, target) in sorted(rows.items()))).encode('ascii')


def decoder_map(table, tree):
    """Read every internal-node prefix using only its actual known tape bits.

    The caller must also compare the returned q/subtree relation to the intended
    relation. Merely reaching an arbitrary state is not sufficient validation.
    """
    groups = defaultdict(set)
    paths = defaultdict(list)
    def visit(node, prefix, state):
        if s.leaf(node):
            return
        groups[state].add(node); paths[state].append(prefix)
        for bit in (0, 1):
            if s.leaf(node[bit]):
                continue
            tape = {i: int(value) for i, value in enumerate(prefix + str(bit))}
            tape[-1] = 1
            before = tape.copy()
            head, q = len(prefix), state
            for tick in range(100):
                if head == len(prefix) + 1:
                    break
                need(head in tape, 'Decoder read outside known prefix')
                w, d, q = table[q, tape[head]]
                tape[head] = w; head += d
            need(tape == before and head == len(prefix) + 1, 'Decoder prefix changed or did not advance')
            visit(node[bit], prefix + str(bit), q)
    visit(tree, '', 84)
    return groups, paths

