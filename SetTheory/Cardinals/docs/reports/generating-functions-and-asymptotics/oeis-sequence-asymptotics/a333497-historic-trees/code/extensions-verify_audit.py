#!/usr/bin/env python3
"""Independent exact certificate for the order-30 historic-tree obstruction."""
from fractions import Fraction
from itertools import combinations
from collections import deque
from pathlib import Path
import json
import os
import sympy as sp

OUT=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).resolve().parent))
r=30
# Construct ascending integer coefficients by repeated integer convolution.
p=[1]
for j in range(r,2*r):
    b=[0]*(len(p)+1)
    for k,a in enumerate(p):
        b[k]+=j*a
        b[k+1]+=a
    p=b
p[0]*=-1  # subtract twice the constant product
# Synthetic division by mu-1, using descending coefficients.
a=p[::-1]
q=[a[0]]
for c in a[1:-1]: q.append(c+q[-1])
assert a[-1]+q[-1]==0
N=len(q)-1
W=(N+2)//2
rows=[]
for parity in [0,1]:
    row=list(map(Fraction,q[parity::2]))
    rows.append(row+[Fraction(0)]*(W-len(row)))
for k in range(2,N+1):
    above,prev=rows[-2],rows[-1]
    assert prev[0]!=0
    row=[(prev[0]*above[j+1]-above[0]*prev[j+1])/prev[0] for j in range(W-1)]+[Fraction(0)]
    assert any(row)
    rows.append(row)
first=[row[0] for row in rows]
assert all(first)
signs=[1 if a>0 else -1 for a in first]
changes=sum(a!=b for a,b in zip(signs,signs[1:]))
assert signs==[1]*28+[-1,1] and changes==2
mu,w=sp.symbols('mu w')
P=sp.Poly.from_list(a,mu)
assert P.eval(1)==0 and P.eval(0)!=0
assert sp.gcd(P,P.diff()).degree()==0
real=sp.Poly(sum(c*(-1)**(j//2)*w**(j//2) for j,c in enumerate(p) if j%2==0),w)
imag_over_omega=sp.Poly(sum(c*(-1)**((j-1)//2)*w**((j-1)//2) for j,c in enumerate(p) if j%2),w)
assert sp.gcd(real,imag_over_omega).degree()==0

# Exterior power signs and graph reachability from integer combinatorics only.
k=3
states=list(combinations(range(r),k)); index={s:i for i,s in enumerate(states)}
adj=[[] for _ in states]; rev=[[] for _ in states]
for source,S in enumerate(states):
    for j in S:
        i=(j-1)%r
        if i in S: continue
        T=tuple(sorted(set(S)-{j}|{i}))
        assert (-1)**(S.index(j)+T.index(i))==1
        target=index[T]
        adj[source].append(target); rev[target].append(source)
assert all(len(a)==len(b) for a,b in zip(adj,rev))
def reachable(graph):
    seen={0}; todo=deque([0])
    while todo:
        for v in graph[todo.popleft()]:
            if v not in seen: seen.add(v);todo.append(v)
    return len(seen)
assert reachable(adj)==reachable(rev)==len(states)==4060
r4=sp.prod(mu+j for j in range(4,8))-2*sp.prod(range(4,8))
assert sp.expand(r4-(mu-1)*(mu+12)*(mu**2+11*mu+70))==0

record={
 'r':r,'polynomial_ascending':p,'quotient_descending':q,
 'routh_first_column':[str(x) for x in first],
 'routh_signs':signs,'quotient_rhp_roots':changes,
 'full_rhp_roots':3,'full_lhp_roots':27,
 'gcd_polynomial_derivative':'1','gcd_imaginary_parts':'1',
 'compound_vertices':len(states),'compound_edges':sum(map(len,adj)),
 'compound_forward_reachable':reachable(adj),'compound_reverse_reachable':reachable(rev),
 'compound_all_edge_signs':1,'compound_indegree_equals_outdegree':True,
 'r4_factorization':'(mu-1)*(mu+12)*(mu^2+11*mu+70)'
}
(OUT/'certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: r=30 exactly 3 RHP, 27 LHP, simple roots; no imaginary roots.')
print('PASS: compound order 3 has 4060 vertices, 11340 positive edges, strongly connected.')
print('PASS: r=4 factorization and stable eigenvalues -12, (-11 +/- i sqrt(159))/2.')
