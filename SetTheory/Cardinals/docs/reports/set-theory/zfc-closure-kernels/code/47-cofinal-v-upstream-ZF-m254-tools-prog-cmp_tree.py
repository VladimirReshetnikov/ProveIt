"""Compare paths.json (p254 decoder tree) with the unfolding of the Wade DAG of source_local.py."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
LOGIC = os.path.normpath(os.path.join(HERE, '..', '..', 'logic'))
sys.path.insert(0, LOGIC)
from build_dag import load_dag
nodes, regidx = load_dag()
print(regidx)
def leaves(n, pre, out):
    for b, e in enumerate(nodes[n]):
        p = pre + str(b)
        if e[0] == 'node':
            leaves(e[1], p, out)
        else:
            out.append((p, e))
L = []
leaves('main().0', '', L)
print('dag leaves', len(L))
paths = json.load(open(os.path.join(HERE, '..', '..', 'inputs', 'paths.json')))
print('p254 leaves', len(paths))
def fmt(e):
    if e[0] == 'op':
        return '3.%s.%s' % (e[1], e[2])
    if e[0] in ('break', 'continue'):
        return '_%s.%d' % (e[0], e[1])
    return e[0]
A = {p: fmt(e) for p, e in L}
B = {p: o for p, o in paths}
same = sum(1 for p in A if B.get(p) == A[p])
print('same path+op', same, 'paths only in dag', len(set(A) - set(B)), 'only in p254', len(set(B) - set(A)))
from collections import Counter
print(Counter(o for o in B.values()).most_common(30))
print(max(len(p) for p in B), max(len(p) for p in A))
