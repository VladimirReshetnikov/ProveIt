"""Check the RMEquiv well-formedness (no break/continue escapes the root) of the tree from paths.json."""
import json, sys
sys.setrecursionlimit(100000)
paths = json.load(open(sys.argv[1]))
leaf = {p[3:]: op for p, op in paths}
def lvl(op, kind):
    if kind == 'b':
        if op.startswith('_break.'): return int(op.split('.')[1])
        if op.endswith('.decnz'): return 1
        return 0
    return int(op.split('.')[1]) if op.startswith('_continue.') else 0
def BC(p):
    """(B, C) for internal node with prefix p, per RMEquiv.wf_escape minimal tables"""
    res = []
    for b in '01':
        q = p + b
        if q in leaf: res.append((lvl(leaf[q], 'b'), lvl(leaf[q], 'c')))
        else: res.append(BC(q))
    (b0, c0), (b1, c1) = res
    return (max(b0 - 1, b1, 0), max(c0, c1 - 1, 0))
print('root (B, C) =', BC(''))
