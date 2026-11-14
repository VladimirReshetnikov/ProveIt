#!/usr/bin/env python3
"""Reproduce a rejected 208-state grammar shortcut and a finite counterexample.

Default inputs are frozen Plain U209 files beside this script. No network,
symbolic engine, third-party dependency, or proof-assistant installation needed.
This rejects a claimed primitive simulation; it says nothing about blank-input
nonhalting of the exploratory table.
"""
from pathlib import Path
import argparse
import hashlib
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_table(path):
    out = {}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        need(key not in out, 'Duplicate transition')
        out[key] = int(write), direction, int(target)
    return out


def encode(table):
    return ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {d} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def tree(rows):
    nodes = {p: (op, arg) for p, op, arg in rows}
    def visit(path):
        if path in nodes:
            return nodes[path]
        return visit(path + '0'), visit(path + '1')
    return visit('')


def leaf(node):
    return isinstance(node[0], str)


def sites(node, path=''):
    if leaf(node):
        return [[path, *node]]
    return sites(node[0], path + '0') + sites(node[1], path + '1')


def boundary(node):
    if leaf(node):
        op, arg = node
        if op == 'CD':
            return 1, 0, False
        if op == 'CB':
            return arg, 0, False
        if op == 'CC':
            return 0, arg, False
        return 0, 0, op == 'CH'
    a, b = boundary(node[0]), boundary(node[1])
    return (max(max(a[0] - 1, 0), b[0]),
            max(a[1], max(b[1] - 1, 0)), a[2] or b[2])


def graph(rows):
    intervals = {}
    for i, (p, op, arg) in enumerate(rows):
        for length in range(len(p) + 1):
            prefix = p[:length]
            lo, hi = intervals.get(prefix, (i, i))
            intervals[prefix] = min(lo, i), i + 1
    def unwind(path, bit, count):
        for j in range(len(path) - 1, -1, -1):
            if path[j] == bit:
                count -= 1
                if count == 0:
                    return intervals[path[:j]][int(bit == '0')] % len(rows)
        return 0
    result = []
    for i, (p, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            targets = [after]
        elif op == 'CD':
            targets = [unwind(p, '0', 1), after]
        elif op == 'CB':
            targets = [unwind(p, '0', arg)]
        elif op == 'CC':
            targets = [unwind(p, '1', arg)]
        else:
            targets = []
        result.append([op, arg, targets])
    return result


def source_node(root, table, wanted):
    found = []
    def visit(node, q):
        if q == wanted:
            found.append(node)
            return
        if leaf(node):
            return
        for b in (0, 1):
            w, d, z = table[q, b]
            if (w, d) == (b, 'R'):
                visit(node[b], z)
    visit(root, 84)
    need(found and len(set(found)) == 1, 'Decoder factor lookup')
    return found[0]


def rotate(root, table, outer, inner):
    node = source_node(root, table, outer)
    a, b = node[0]
    c = node[1]
    need(all(boundary(n) == (0, 0, False) for n in (a, b, c)),
         'Rotation factors are not closed')
    need(table[outer, 0] == (0, 'R', inner), 'Unexpected decoder child')
    need([(q, bit) for (q, bit), value in table.items() if value[2] == inner]
         == [(outer, 0)], 'Additional inner entrance')
    paths = []
    replacement = a, (b, c)
    def replace(n, path=''):
        if n == node:
            paths.append(path)
            return replacement
        if leaf(n):
            return n
        return replace(n[0], path + '0'), replace(n[1], path + '1')
    root = replace(root)
    x, y, z = table[inner, 0][2], table[inner, 1][2], table[outer, 1][2]
    table[outer, 0], table[outer, 1] = (0, 'R', x), (1, 'R', inner)
    table[inner, 0], table[inner, 1] = (0, 'R', y), (1, 'R', z)
    return root, dict(outer=outer, inner=inner, side=0, all_paths=paths,
                     factor_sizes=[len(sites(n)) for n in (a, b, c)])


def canonical_ones(path):
    return frozenset({-1, 56} | {i for i, bit in enumerate(path) if bit == '1'}
                     | {58 + 2 * i for i in range(10)})


def next_boundary(table, rows, initial):
    templates = {canonical_ones(path): i for i, (path, op, arg) in enumerate(rows)}
    tape = set(initial)
    q, head = 84, 0
    trace = []
    for step in range(1, 2001):
        bit = int(head in tape)
        write, direction, target = table[q, bit]
        trace.append([q, head, bit, write, direction, target])
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        q = target
        head += 1 if direction == 'R' else -1
        if q == 84 and head == 0 and frozenset(tape) in templates:
            return dict(steps=step, state=q, head=head, ones=sorted(tape),
                        source_ordinal=templates[frozenset(tape)], trace=trace)
        need(q != 254, 'Unexpected halt during finite witness')
    raise ValueError('No canonical return within witness bound')


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-table', type=Path, default=here / 'baseline209.native.tm')
    parser.add_argument('--baseline-sites', type=Path, default=here / 'baseline209.sites.json')
    parser.add_argument('--output', type=Path, default=here / 'results')
    args = parser.parse_args()
    original = read_table(args.baseline_table)
    rows = json.loads(args.baseline_sites.read_text())
    need(digest(args.baseline_table.read_bytes()) ==
         '891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4',
         'Wrong Plain U209 baseline')
    root, table = tree(rows), dict(original)
    ledger = []
    for outer, inner in ((155, 85), (52, 154)):
        root, record = rotate(root, table, outer, inner)
        ledger.append(record)
    new_rows = sites(root)
    need([r[1:] for r in rows] == [r[1:] for r in new_rows], 'Primitive word changed')
    need(graph(rows) == graph(new_rows), 'Source CFG changed')
    need(table[85, 0] == table[154, 0] == (0, 'R', 12), 'Zero rows differ')
    need(table[85, 1] == table[154, 1] == (1, 'R', 150), 'One rows differ')
    table = {(q, b): (w, d, 85 if z == 154 else z)
             for (q, b), (w, d, z) in table.items() if q != 154}
    need(len(table) == 416, 'Wrong rejected candidate size')
    initial = canonical_ones(rows[25][0])
    baseline_run = next_boundary(original, rows, initial)
    rejected_run = next_boundary(table, new_rows, initial)
    need(graph(rows)[25][2][0] == 28, 'Wrong expected zero-decrement successor')
    need((baseline_run['steps'], baseline_run['source_ordinal']) == (494, 28),
         'Baseline does not reproduce expected result')
    need((rejected_run['steps'], rejected_run['source_ordinal']) == (526, 44),
         'Rejected candidate no longer reproduces counterexample')
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    report = dict(status='REJECTED_GRAMMAR_REDUCTION_REPRODUCED',
                  reason='Wrong primitive successor on a canonical all-zero register frame',
                  baseline_table_sha256=digest(args.baseline_table.read_bytes()),
                  baseline_sites_sha256=digest(args.baseline_sites.read_bytes()),
                  source_word_preserved=True, source_control_graph_preserved=True,
                  rotations=ledger, exact_merge=[154, 85],
                  changed_retained_rows=[dict(state=q, read=b, before=original[q, b], after=v)
                                         for (q, b), v in sorted(table.items())
                                         if v != original[q, b]],
                  initial=dict(state=84, head=0, source_ordinal=25, site=rows[25],
                               registers=[0]*9, gap=0, spare_list=[0], ones=sorted(initial)),
                  expected_successor=rows[28], actual_successor=new_rows[44],
                  baseline_run=baseline_run, rejected_run=rejected_run,
                  scope='Finite canonical-frame simulation counterexample, not a claim about blank-input halting')
    (out / 'rejected208.native.tm').write_bytes(encode(table))
    (out / 'rejected208.sites.json').write_text(json.dumps(new_rows, separators=(',', ':')) + '\n')
    (out / 'rejection.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in
          ('status', 'reason', 'source_word_preserved', 'source_control_graph_preserved',
           'exact_merge', 'expected_successor', 'actual_successor')}, indent=2))


if __name__ == '__main__':
    main()
