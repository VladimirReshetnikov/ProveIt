"""Independent open-path interpreter and literal source transformation helpers."""
from functools import lru_cache
import json


def frozen(x):
    return tuple(map(frozen, x)) if isinstance(x, list) else x


def leaf(t):
    return isinstance(t[0], str)


def leaves(t, path=''):
    return [(path, *t)] if leaf(t) else leaves(t[0], path + '0') + leaves(t[1], path + '1')


def parse(rows):
    lookup = {p: (op, r) for p, op, r in rows}
    assert len(lookup) == len(rows)
    def go(p):
        return lookup[p] if p in lookup else (go(p + '0'), go(p + '1'))
    t = go('')
    assert [list(x) for x in leaves(t)] == rows
    return t


def subtrees(t):
    seen = set()
    def visit(x):
        if x in seen:
            return
        seen.add(x)
        if not leaf(x):
            visit(x[0]); visit(x[1])
    visit(t)
    return seen


@lru_cache(None)
def open_graph(t):
    """Resolve open Break/Continue exits from leaf paths, not subtree signatures.

    Targets are (instruction index, None), or (None, exit tag). Tag0 means
    Normal, tagk Break(k), and tag(8+k) Continue(k).
    """
    rows = leaves(t)
    spans = {}
    for i, (p, _, _) in enumerate(rows):
        for k in range(len(p) + 1):
            prefix = p[:k]
            if prefix not in spans:
                spans[prefix] = [i, i + 1]
            else:
                spans[prefix][1] = i + 1
    normal = (None, 0)
    def after(i):
        return normal if i == len(rows) else (i, None)
    def transfer(p, side, count):
        positions = [i for i, b in enumerate(p) if b == side]
        if len(positions) < count:
            remain = count - len(positions)
            return None, remain if side == '0' else 8 + remain
        prefix = p[:positions[-count]]
        return after(spans[prefix][1]) if side == '0' else (spans[prefix][0], None)
    out = []
    for i, (p, op, r) in enumerate(rows):
        assert op in ('CI', 'CD', 'CB', 'CC')
        if op in ('CI', 'CD'):
            assert r in (5, 6)
        targets = (after(i + 1),) if op == 'CI' else (transfer(p, '0', 1), after(i + 1)) if op == 'CD' else (transfer(p, '0' if op == 'CB' else '1', r),)
        out.append((op, r, targets))
    return tuple(out)


def evaluate(t, a, b, bound=9):
    graph = open_graph(t)
    pc = 0
    values = [a, b]
    seen = set()
    while True:
        state = pc, *values
        if state in seen:
            return -1
        seen.add(state)
        op, reg, targets = graph[pc]
        if op == 'CI':
            values[reg - 5] += 1
            if values[reg - 5] > bound:
                return -1
            target = targets[0]
        elif op == 'CD':
            branch = int(values[reg - 5] != 0)
            values[reg - 5] -= branch
            target = targets[branch]
        else:
            target = targets[0]
        pc, tag = target
        if pc is None:
            return 16 * (values[0] * (bound + 1) + values[1]) + tag


def signature(t, bound=9):
    return [evaluate(t, a, b, bound) for a in range(bound + 1) for b in range(bound + 1)]


def replacement(t, old, new):
    if t == old:
        return new, 1
    if leaf(t):
        return t, 0
    left, a = replacement(t[0], old, new)
    right, b = replacement(t[1], old, new)
    return (left, right), a + b


def metrics(t):
    rows = leaves(t)
    return {'dag_nodes': len(subtrees(t)), 'leaf_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(s) for p, _, _ in rows for s in p.split('1'))}
