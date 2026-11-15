"""Exact source paths and guarded-successor resolution for the frozen tree."""

def tuples(x):
    return tuple(map(tuples, x)) if isinstance(x, list) else x

def resolve(node_data, grammar):
    nodes = {k: tuples(v) for k, v in node_data.items()}
    rules = grammar['rules']
    def expand(x):
        return tuple(expand(y) for y in rules[x]) if isinstance(x, str) and x in rules else tuples(x)
    ax = expand(grammar['root'])
    sites = []
    def walk(tree, path):
        if isinstance(tree, str):
            return walk(ax if tree == 'x67' else nodes[tree], path)
        if tree[0] == 'leaf':
            sites.append((path, tree[1], tree[2])); return
        walk(tree[0], path + (0,)); walk(tree[1], path + (1,))
    walk('node172', ())
    index = {p: i for i, (p, _, _) in enumerate(sites)}
    def locate(p):
        if p in index: return index[p]
        for i, (q, _, _) in enumerate(sites):
            if q[:len(p)] == p or (p[:len(q)] == q and not any(p[len(q):])): return i
        raise AssertionError(('missing address', p))
    def after(p):
        for i in range(len(p) - 1, -1, -1):
            if p[i] == 0: return locate(p[:i] + (1,))
        raise AssertionError(('unexpected root exit', p))
    def cut(p, bit, count):
        for i in range(len(p) - 1, -1, -1):
            if p[i] == bit:
                count -= 1
                if count == 0: return p[:i]
        raise AssertionError(('invalid branch tag', p, bit, count))
    instructions = []
    for p, op, a in sites:
        if op == 'inc': ins = ['inc', a, after(p)]
        elif op == 'dec': ins = ['dec', a, after(cut(p, 0, 1)), after(p)]
        elif op == 'breakTo': ins = ['jump', after(cut(p, 0, a))]
        elif op == 'continueTo': ins = ['jump', locate(cut(p, 1, a))]
        else:
            assert op == 'halt'; ins = ['halt']
        instructions.append(ins)
    return [[''.join(map(str, p)), op, a] for p, op, a in sites], instructions
