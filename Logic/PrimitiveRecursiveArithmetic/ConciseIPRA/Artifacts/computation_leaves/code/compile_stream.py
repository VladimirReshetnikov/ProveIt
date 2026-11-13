"""Independent untrusted producer for goal-directed computation certificates.

Parses an accepted certificate of the pinned three-field supply checker into
its actual inference tree, then inlines computational assumptions at their
uses. This finite producer is not part of the measured trusted checker.
"""
import json
import sys
from pathlib import Path
sys.setrecursionlimit(50000)


def op(a, t=None, d=0, k=0):
    if isinstance(a, list):
        return [op(b, t, d + 5 - len(a), k) for b in a]
    if k <= a < d:
        return a
    return d % 2 and op(t, d=3, k=k)


def rename(a, env):
    if isinstance(a, list):
        return [rename(x, env) for x in a]
    return env.get(a, a) if isinstance(a, int) and a < 0 else a


def parse_old(records):
    it = iter(records)
    goal = next(it)
    counts = {}
    def parse(k, a, g):
        ia = op(a, k=k)
        if ia in g:
            counts['hyp'] = counts.get('hyp', 0) + 1
            return {'kind': 'hyp', 'goal': a, 'k': k}
        row = next(it)
        s, u, t = row
        r = row
        old = a
        dispatch = 'open'
        if op(t, u, k=k) == a:
            a = op(t, s, k=k)
            s = r[:2] if s else [t] * 3
            u = 0
            dispatch = 'replace' if r[0] else 'specialize'
        major = None
        if u:
            h = [[s and [s], u, t], op(t, r, 3, k) if s else u]
            dispatch = 'supply'
        else:
            if s:
                major = parse(k, s, g)
                h = s * 3
            else:
                major = parse(k, s, g)
                a = op(*a, t, 2, k=k)
                h = a
                dispatch = 'introduce'
        k2 = k - 1
        h2 = op(h, k2 * (1 if s else len(a) == 2), k=k2)
        a2 = op(a, [k2], k=k2)
        counts[dispatch] = counts.get(dispatch, 0) + 1
        return {'kind': dispatch, 'goal': old, 'k': k, 'row': row,
                'major': major, 'hyp': h2,
                'next': parse(k2, a2, g + [h2])}
    tree = parse(0, goal, [0])
    try:
        next(it)
    except StopIteration:
        return tree, counts
    raise ValueError('Unconsumed input in source certificate')


def computation(a, k):
    if not isinstance(a, list) or len(a) != 2:
        return None
    left, right = a
    if not isinstance(left, list) or len(left) != 3:
        return None
    counter, seed, body = left
    if not counter:
        source = counter
    elif isinstance(counter, list) and len(counter) == 1:
        source = counter[0]
    else:
        return None
    r = [source, seed, body]
    got = [[source and [source], seed, body], op(body, r, 3, k) if source else seed]
    return r if got == a else None


def compile_tree(tree, global_floor=False):
    counts = {}
    def emit(node, k, a, g, env):
        assert a == rename(node['goal'], env), ('goal', node['kind'], a, rename(node['goal'], env))
        if op(a, k=k) in g:
            counts['hyp'] = counts.get('hyp', 0) + 1
            return [], k
        comp = computation(a, k)
        if comp is not None:
            counts['compute'] = counts.get('compute', 0) + 1
            return [comp], k
        kind = node['kind']
        if kind == 'supply':
            env2 = env | {node['k'] - 1: 0}
            counts['erased_supply'] = counts.get('erased_supply', 0) + 1
            return emit(node['next'], k, a, g, env2)
        if kind == 'hyp':
            raise ValueError(('Missing retained hypothesis or recognizable computation', a))
        row = rename(node['row'], env)
        s, u, t = row
        preview = [[s and [s], u, t], op(t, row, 3, k) if s else u]
        assert preview != a
        major_records = []
        a1 = a
        if op(t, u, k=k) == a:
            a1 = op(t, s, k=k)
            s = row[:2] if s else [t] * 3
        if s:
            major_records, km = emit(node['major'], k, s, g, env)
            if global_floor:
                k = km
            h = s * 3
        else:
            a1 = op(*a1, t, 2, k=k)
            h = a1
        k2 = k - 1
        env2 = env | {node['k'] - 1: k2}
        h2 = op(h, k2 * (1 if s else len(a1) == 2), k=k2)
        a2 = op(a1, [k2], k=k2)
        counts[kind] = counts.get(kind, 0) + 1
        tail, kfinal = emit(node['next'], k2, a2, g + [h2], env2)
        return [row] + major_records + tail, kfinal
    goal = tree['goal']
    rows, _ = emit(tree, 0, goal, [0], {})
    return [goal] + rows, counts


def main():
    source = Path(sys.argv[1])
    destination = Path(sys.argv[2])
    tree, before = parse_old([json.loads(x) for x in source.read_text().splitlines() if x.strip()])
    result, after = compile_tree(tree, '--global' in sys.argv)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(''.join(json.dumps(x, separators=(',', ':')) + '\n' for x in result))
    print(json.dumps({'source': str(source), 'destination': str(destination), 'before': before, 'after': after, 'records': len(result) - 1}, sort_keys=True))


if __name__ == '__main__':
    main()
