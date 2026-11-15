#!/usr/bin/env python3
"""Reconstruct four source-preserving 194-state loop-continuation machines.

Standard library only.  The independent, literal-row universal verification
is verification/check.py.  Neither program is a Lean kernel or an absolute
iPRA/Con(PA) calibration.  See report/report.pdf for the mathematical scope.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'reference' / 'primary'
INC = ('leaf', 'inc', 1)
START, HALT = 74, 254


def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert (q, b) not in rows and b in (0, 1) and w in (0, 1)
        assert d in ('L', 'R')
        rows[q, b] = w, d == 'R', n
    return rows


def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))


def grammar(path):
    data = json.loads(path.read_text())
    def go(t):
        if isinstance(t, list):
            return tup(t)
        return tuple(go(x) for x in data['rules'][t]) if t in data['rules'] else t
    return go(data['root'])


def source(nodes, ax):
    """Flatten the tree and resolve every branch, including counted returns."""
    sites = []
    def walk(t, path):
        if isinstance(t, str):
            return walk(ax if t == 'x67' else nodes[t], path)
        if t[0] == 'leaf':
            sites.append((path, t[1], t[2]))
            return
        walk(t[0], path + '0')
        walk(t[1], path + '1')
    walk('node172', '')
    by_path = {p: i for i, (p, _, _) in enumerate(sites)}
    assert len(by_path) == len(sites)
    def locate(p):
        if p in by_path:
            return by_path[p]
        for i, (q, _, _) in enumerate(sites):
            if q.startswith(p) or (p.startswith(q) and set(p[len(q):]) <= {'0'}):
                return i
        raise AssertionError(('unresolved path', p))
    def after(p):
        for i in range(len(p)-1, -1, -1):
            if p[i] == '0':
                return locate(p[:i] + '1')
        raise AssertionError(('escaped source', p))
    def cut(p, bit, count):
        for i in range(len(p)-1, -1, -1):
            if p[i] == bit:
                count -= 1
                if count == 0:
                    return p[:i]
        raise AssertionError(('return exceeds scope', p, bit, count))
    instructions = []
    for p, op, arg in sites:
        if op == 'inc':
            ins = ['inc', arg, after(p)]
        elif op == 'dec':
            ins = ['dec', arg, after(cut(p, '0', 1)), after(p)]
        elif op == 'breakTo':
            ins = ['jump', after(cut(p, '0', arg))]
        elif op == 'continueTo':
            ins = ['jump', locate(cut(p, '1', arg))]
        elif op == 'halt':
            ins = ['halt']
        else:
            raise AssertionError(op)
        instructions.append(ins)
    return sites, instructions


def reachable(rows):
    seen, todo = {START}, [START]
    for q in todo:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != HALT and n not in seen:
                seen.add(n)
                todo.append(n)
    return {k: v for k, v in rows.items() if k[0] in seen}


def compile_loop(base, tree):
    """Reuse literal existing reader rows; allocate only missing binary nodes."""
    rows = {k: v for k, v in base.items() if k[0] not in (139, 190)}
    signatures = {(rows[q, 0], rows[q, 1]): q for q, _ in rows}
    ids, next_state = {}, 330
    def action(t, bit):
        nonlocal next_state
        if t == INC:
            return bit, True, 61
        if t[0] == 'leaf':
            assert t[1] == 'continueTo' and t[2] in (2, 3)
            return (0, False, 16) if t[2] == 2 else (1, False, 73)
        if t in ids:
            return bit, True, ids[t]
        pair = action(t[0], 0), action(t[1], 1)
        q = signatures.get(pair)
        if q is None:
            q, next_state = next_state, next_state + 1
            rows[q, 0], rows[q, 1] = pair
            signatures[pair] = q
        ids[t] = q
        return bit, True, q
    a0, a1 = action(tree[0], 0), action(tree[1], 1)
    rows[139, 0], rows[139, 1] = a0, a1
    return reachable(rows)


def rename(rows, mapping):
    return {(mapping.get(q, q), b): (w, d, mapping.get(n, n))
            for (q, b), (w, d, n) in rows.items()}


def apply_folds(rows, folds):
    aliases = {a: b for a, b, _ in folds}
    actions = {b: acts for a, b, acts in folds}
    assert len({q for a, b, _ in folds for q in (a, b)}) == 2 * len(folds)
    result = {}
    for (q, bit), act in rows.items():
        if q in aliases:
            continue
        w, d, n = actions[q][bit] if q in actions else act
        result[q, bit] = w, bool(d), aliases.get(n, n)
    return result, aliases


def check_folds(raw, folded, aliases, folds):
    incoming, cases = {}, []
    for (q, bit), (w, d, n) in raw.items():
        incoming.setdefault(n, []).append([q, bit, w, d, n])
    for a, b, _ in folds:
        assert START not in (a, b)
        assert {(r[2], r[3]) for r in incoming[a]} == {(0, True)}
        assert {(r[2], r[3]) for r in incoming[b]} == {(1, True)}
        for old, history in ((a, 0), (b, 1)):
            for bit in (0, 1):
                w, d, n = raw[old, bit]
                target = aliases.get(n, n), 1 if d else -1, {-1: history, 0: w}
                q, pos, tape = b, 0, {-1: history, 0: bit}
                trace = [[q, pos, tape[-1], tape[0]]]
                for steps in range(1, 21):
                    assert pos in (-1, 0)
                    w, d, q = folded[q, tape[pos]]
                    tape[pos] = w
                    pos += 1 if d else -1
                    trace.append([q, pos, tape[-1], tape[0]])
                    if (q, pos, tape) == target:
                        break
                else:
                    raise AssertionError(('fold failed', old, bit))
                cases.append(dict(old_state=old, history=history, read=bit,
                                  steps=steps, trace=trace))
    return dict(cases=cases, count=len(cases), simultaneous=True)


def dense(rows):
    states = {q for q, _ in rows}
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert {n for _, _, n in rows.values()} - states == {HALT}
    order, ids = [START], {START: 0}
    for q in order:
        for bit in (0, 1):
            n = rows[q, bit][2]
            if n != HALT and n not in ids:
                ids[n] = len(order)
                order.append(n)
    assert len(order) == len(states)
    result = {(ids[q], b): (w, d, len(states) if n == HALT else ids[n])
              for (q, b), (w, d, n) in rows.items()}
    return result, order + [HALT]


def startup(rows, path):
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected_head = -2
    expected = {expected_head - 1, expected_head + 48}
    expected.update(expected_head+i for i, b in enumerate(path) if b == '1')
    pos = expected_head + 49
    for v in physical:
        pos += 1
        expected.update(range(pos, pos+v+1))
        pos += v+1
    q, head, ones = START, 0, set()
    for steps in range(1, 100001):
        w, d, q = rows[q, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        assert q != HALT
        if (q, head, ones) == (84, expected_head, expected):
            return dict(steps=steps, state=q, head=head, physical_file=physical,
                        logical_registers=[2]+[0]*8, gap=0, spare_ones=26,
                        one_cells=sorted(ones), complete_tape_equality=True)
    raise AssertionError('Exact startup frame was not reached')


def load_inputs():
    for name, expected in json.loads((INPUT/'INPUT_HASHES.json').read_text()).items():
        assert sha(INPUT/name) == expected, name
    raw = read_table(INPUT/'raw.native.tm')
    nodes = {k: tup(v) for k, v in json.loads((INPUT/'nodes.json').read_text()).items()}
    ax = grammar(INPUT/'grammar.json')
    sites, ins = source(nodes, ax)
    assert ins == json.loads((INPUT/'instructions.json').read_text())
    assert json.loads(json.dumps(sites)) == json.loads((INPUT/'sites.json').read_text())
    folds = json.loads((INPUT/'folds.json').read_text())
    parent, aliases = apply_folds(raw, folds)
    check_folds(raw, parent, aliases, folds)
    assert parent == read_table(INPUT/'machine.native.tm')
    parent_dense, _ = dense(parent)
    assert table_text(parent_dense) == (INPUT/'machine.tm').read_text()
    assert sha(INPUT/'machine.tm') == '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
    return raw, nodes, ax, sites, ins, parent


def build(name, config, destination):
    raw0, nodes, ax, old_sites, old_ins, parent = load_inputs()
    tree = tup(config['tree'])
    nodes['node62'] = tree
    sites, ins = source(nodes, ax)
    assert ins == old_ins and len(ins) == 3673
    raw = compile_loop(raw0, tree)
    folds = config['folds']
    if config['rename_330_to_190']:
        assert all(q != 190 for q, _ in raw)
        raw = rename(raw, {330: 190})
    rows, aliases = apply_folds(raw, folds)
    local = check_folds(raw, rows, aliases, folds)
    table, labels = dense(rows)
    assert len(rows) == 388 and len(labels) == 195
    text = table_text(table)
    assert hashlib.sha256(text.encode()).hexdigest() == config['expected_dense_sha256']
    seed = startup(rows, sites[25][0])
    assert seed['steps'] == config['startup_steps']
    binding = dict(source_sites=3673, source_outcomes=4780,
                   all_instructions_and_targets_identical=True,
                   changed_addresses=sum(a[0] != b[0] for a, b in zip(old_sites, sites)),
                   maximum_address_length=max(len(p) for p, _, _ in sites))
    changes = [dict(state=q, read=b, old=parent.get((q,b)), new=rows.get((q,b)))
               for q, b in sorted(set(parent) | set(rows)) if parent.get((q,b)) != rows.get((q,b))]
    if name == 'PA194LC':
        assert [(r['state'], r['read']) for r in changes] == [(139,0),(139,1),(190,1)]
    destination.mkdir(parents=True, exist_ok=True)
    for filename, data in [('machine.tm', table), ('machine.native.tm', rows), ('raw.native.tm', raw)]:
        (destination/filename).write_text(table_text(data))
    for filename, data in [('labels.json',labels),('nodes.json',nodes),('sites.json',sites),
                           ('instructions.json',ins),('folds.json',folds),('local_folds.json',local),
                           ('source_binding.json',binding),('native_changes.json',changes)]:
        dump(destination/filename, data)
    receipt = dict(name=name, states=194, rows=388, start=0, halt=194,
                   raw_states=len(raw)//2, folds=len(folds), startup=seed,
                   source_binding=binding, dense_sha256=sha(destination/'machine.tm'),
                   native_sha256=sha(destination/'machine.native.tm'),
                   independent_runtime_check='Run verification/check.py on this output.',
                   absolute_ipra_consistency_equivalence_established=False,
                   new_kernel_checked_lean_endpoint=False)
    dump(destination/'receipt.json', receipt)
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('startup',)},sort_keys=True), flush=True)
    return receipt


if __name__ == '__main__':
    assert __debug__ and not sys.flags.optimize, 'Assertions must be enabled.'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'machines')
    parser.add_argument('--only',choices=['PA194LC','PA194LC_A','PA194LC_B','PA194LC_C'])
    args = parser.parse_args()
    variants = json.loads((Path(__file__).parent/'variants.json').read_text())
    for name, config in variants.items():
        if args.only is None or name == args.only:
            build(name, config, args.output/name)
