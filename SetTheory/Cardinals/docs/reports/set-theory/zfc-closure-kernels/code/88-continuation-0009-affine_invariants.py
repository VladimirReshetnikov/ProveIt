"""Exact rational affine reachability over the guarded source control graph.

Represent affine sets as homogeneous linear spans of integer vectors. All
elimination is fraction free; gcd normalization is mathematical exactness,
not numerical rank estimation. Positive guards discard only a space whose
tested coordinate is identically zero. Remaining positivity is relaxed.
"""
from collections import deque, Counter
from functools import reduce
from math import gcd
from fractions import Fraction
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
INPUTS = ROOT / 'experiments/audit_inputs'
data = json.loads((INPUTS / 'quotient.json').read_text())
G = data['graph']
WIDTH = 10
INTERVAL_PATH = INPUTS / 'interval-invariants.json'
INTERVALS = json.loads(INTERVAL_PATH.read_text())['invariants']
REDUCED = False

def primitive(v):
    d = reduce(gcd, v)
    if not d:
        return tuple(v)
    a = next(x for x in v if x)
    if a < 0:
        d = -d
    return tuple(x // d for x in v)

def eliminate(v, row, pivot):
    if not v[pivot]:
        return v
    a, b = row[pivot], v[pivot]
    return primitive(tuple(a*x-b*y for x, y in zip(v, row)))

def add(basis, vector):
    v = tuple(vector)
    for p, row in sorted(basis.items()):
        v = eliminate(v, row, p)
    if not any(v):
        return False
    v = primitive(v)
    p = next(i for i, x in enumerate(v) if x)
    for q, row in list(basis.items()):
        basis[q] = eliminate(row, v, p)
    basis[p] = v
    return True

def canonical(vectors):
    basis = {}
    for v in vectors:
        add(basis, v)
    return basis

def zero_slice(basis, register):
    pivot = next((b for b in basis.values() if b[register]), None)
    if pivot is None:
        return basis
    rows = []
    for row in basis.values():
        v = primitive(tuple(pivot[register]*x-row[register]*y
                            for x, y in zip(row, pivot)))
        if any(v):
            rows.append(v)
    if not any(row[-1] for row in rows):
        return {}
    return canonical(rows)

def constrain(basis, functional):
    values = [(row, sum(a*b for a,b in zip(row,functional))) for row in basis.values()]
    pivot = next(((row,v) for row,v in values if v), None)
    if pivot is None:
        return basis
    chosen, value = pivot
    rows = [primitive(tuple(value*a-v*b for a,b in zip(row,chosen))) for row,v in values]
    if not any(row[-1] for row in rows):
        return {}
    return canonical(rows)

def equations(basis):
    for free in set(range(WIDTH))-set(basis):
        v = [Fraction(0)]*WIDTH
        v[free] = Fraction(1)
        for pivot,row in basis.items():
            v[pivot] = -Fraction(row[free],row[pivot])
        denominator = 1
        for f in v:
            denominator = denominator*f.denominator//gcd(denominator,f.denominator)
        yield primitive([int(f*denominator) for f in v])

def reduce_at(index, basis):
    interval = INTERVALS[index]
    if interval is None:
        return {}
    for r,(lo,hi) in enumerate(interval):
        if lo == hi:
            f=[0]*WIDTH;f[r]=1;f[-1]=-lo
            basis=constrain(basis,f)
            if not basis:return {}
    # Exact elementary nonnegativity reduction: a sum of terms known
    # nonnegative can vanish only when each nonzero term vanishes.
    while basis:
        old_dimension=len(basis)
        for eq in list(equations(basis)):
            for sign in (1,-1):
                f=[sign*x for x in eq]
                if not all(x>=0 for x in f[:9]):continue
                minimum=f[-1]+sum(f[r]*INTERVALS[index][r][0] for r in range(9))
                if minimum>0:return {}
                if minimum==0:
                    for r in range(9):
                        if f[r]:
                            g=[0]*WIDTH;g[r]=1;g[-1]=-INTERVALS[index][r][0]
                            basis=constrain(basis,g)
                            if not basis:return {}
        if len(basis)==old_dimension:break
    return basis

def shift(basis, register, delta):
    result = []
    for row in basis.values():
        v = list(row)
        v[register] += delta*v[-1]
        result.append(tuple(v))
    return result

def transfers(node, basis):
    op, successors = G[node]
    if not basis:
        return []
    if op[0] == 'I':
        return [(successors[0], shift(basis, op[1], 1), 'increment')]
    if op[0] == 'D':
        r = op[1]
        positive = shift(basis, r, -1) if any(v[r] for v in basis.values()) else []
        if REDUCED and INTERVALS[node][r][1]==0:positive=[]
        zero = list(zero_slice(basis, r).values())
        if REDUCED and INTERVALS[node][r][0]>0:zero=[]
        return [(successors[0], positive, 'positive'),
                (successors[1], zero, 'zero')]
    return [(j, list(basis.values()), 'control') for j in successors]

def main():
    start = time.monotonic()
    states = [{} for _ in G]
    initial = (3,0,0,0,3,0,0,0,0,1)
    assert add(states[0], initial)
    queue = deque([0]); pending = {0}; pops = updates = 0
    while queue:
        i = queue.popleft(); pending.remove(i); pops += 1
        for j, vectors, _ in transfers(i, states[i]):
            if REDUCED:
                vectors=list(reduce_at(j,canonical(vectors)).values())
            changed = False
            for vector in vectors:
                changed = add(states[j], vector) or changed
            if changed:
                updates += 1
                if j not in pending:
                    queue.append(j); pending.add(j)
        if pops % 10000 == 0:
            print('progress', pops, updates, len(queue), round(time.monotonic()-start, 2), flush=True)
    # Independently replay every finite transfer inclusion for the fixed point.
    edges = 0; rejected = []
    for i, basis in enumerate(states):
        for j, vectors, kind in transfers(i, basis):
            if REDUCED:
                vectors=list(reduce_at(j,canonical(vectors)).values())
            if not vectors:
                rejected.append([i,kind])
            for v in vectors:
                assert not add(dict(states[j]), v), (i,j,kind)
            edges += 1
    out = {
        'status':'PASS', 'domain':'exact rational affine spans',
        'initial':list(initial), 'states':[list(b.values()) for b in states],
        'dimension_counts':dict(Counter(len(b)-1 for b in states)),
        'excluded_leaves':[i for i,b in enumerate(states) if not b],
        'excluded_guard_edges':rejected, 'checked_edges':edges,
        'worklist_pops':pops, 'join_updates':updates,
        'elapsed_seconds':time.monotonic()-start,
        'scope':'Inductive overapproximation, not an exact reachable-state set.'
    }
    out['reduced_with_interval_certificate']=REDUCED
    (Path.cwd()/('reduced_affine_certificate.json' if REDUCED else 'affine_invariant_certificate.json')).write_text(json.dumps(out, separators=(',',':'))+'\n')
    print({k:v for k,v in out.items() if k!='states'}, flush=True)

if __name__ == '__main__':
    import sys
    REDUCED='--reduced' in sys.argv
    main()
