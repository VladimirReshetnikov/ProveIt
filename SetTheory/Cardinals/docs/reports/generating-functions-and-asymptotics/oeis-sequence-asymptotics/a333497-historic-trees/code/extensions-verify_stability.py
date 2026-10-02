#!/usr/bin/env python3
"""Exact reproducible stability and cone-irreducibility certificates.
Python stdlib for Routh and graph checks; SymPy for independent root counting.
No floating-point arithmetic enters any certificate.
"""
from math import prod,gcd
from functools import reduce
from itertools import combinations
from collections import deque
from pathlib import Path
import json
import os
import sympy as sp
ROOT=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).resolve().parent))

def polynomial_coefficients(r):
    c=[1]
    for j in range(r,2*r):
        d=[0]*(len(c)+1)
        for k,v in enumerate(c):d[k]+=v;d[k+1]+=v*j
        c=d
    c[-1]-=2*prod(range(r,2*r))
    q=[c[0]]
    for v in c[1:-1]:q.append(v+q[-1])
    assert c[-1]+q[-1]==0 # p(1)=0 and exact synthetic division
    return c,q

def routh_primitive(c):
    """Positive rescalings of the standard Routh rows, using integers only."""
    n=len(c)-1; width=(n+2)//2
    rows=[c[::2]+[0]*(width-len(c[::2])),c[1::2]+[0]*(width-len(c[1::2]))]
    for k in range(2,n+1):
        a,b=rows[-2:];assert b[0]!=0
        # Standard numerator divided by b[0]; instead multiply by sign(b[0]).
        sg=1 if b[0]>0 else -1
        cc=[sg*(b[0]*a[j+1]-a[0]*b[j+1]) for j in range(width-1)]+[0]
        g=reduce(gcd,cc);assert g>0 # no all-zero row
        rows.append([v//g for v in cc])
    rows=rows[:n+1]
    assert all(row[0] for row in rows)
    signs=[1 if row[0]>0 else -1 for row in rows]
    count=sum(a!=b for a,b in zip(signs,signs[1:]))
    return rows,signs,count

cert=[]
for r in range(2,41):
    p,q=polynomial_coefficients(r)
    rows,signs,count=routh_primitive(q)
    assert count==(0 if r<=29 else 2)
    cert.append({'r':r,'q_coefficients':list(map(str,q)),
      'first_column':[str(row[0]) for row in rows], 'signs':signs,
      'right_half_plane_q':count})
(ROOT/'routh_certificates_2_40.json').write_text(json.dumps(cert,indent=2))

mu=sp.symbols('mu');independent=[]
for r in (29,30):
    pc,qc=polynomial_coefficients(r);p=sp.Poly.from_list(pc,mu);q=sp.Poly.from_list(qc,mu)
    g=sp.gcd(p,p.diff());assert g.degree()==0
    re=sp.Poly(sum((-1)**(j//2)*q.nth(j)*mu**j for j in range(0,r,2)),mu)
    im=sp.Poly(sum((-1)**((j-1)//2)*q.nth(j)*mu**j for j in range(1,r,2)),mu)
    gi=sp.gcd(re,im);assert gi.degree()==0 # no roots on imaginary axis
    n=q.count_roots(-200*sp.I,2+200*sp.I)
    assert n==(0 if r==29 else 2)
    independent.append({'r':r,'gcd_p_pprime':str(g.as_expr()),
      'gcd_Re_q_iw_Im_q_iw':str(gi.as_expr()),
      'rectangle':['0-200i','2+200i'],'q_roots':int(n),
      'method':'SymPy exact complex Cauchy-index root counting'})
(ROOT/'independent_complex_root_counts.json').write_text(json.dumps(independent,indent=2))

n=30;k=3;states=list(combinations(range(n),k));adj={x:[] for x in states};rev={x:[] for x in states}
for x in states:
    for j in x:
        i=(j-1)%n
        if i not in x:
            y=tuple(sorted((set(x)-{j})|{i}));adj[x].append(y);rev[y].append(x)
def reachable(g):
    seen={(0,1,2)};queue=deque(seen)
    while queue:
        for y in g[queue.popleft()]:
            if y not in seen:seen.add(y);queue.append(y)
    return len(seen)
f,b=reachable(adj),reachable(rev);assert f==b==len(states)==4060
obj={'n':n,'k':k,'vertices':len(states),'edges':sum(map(len,adj.values())),
     'forward_reachable':f,'reverse_reachable':b,
     'all_additive_compound_offdiagonal_signs':'+: adjacent moves sign+; wrap sign (-1)^(k-1)=+'}
(ROOT/'compound_graph_certificate.json').write_text(json.dumps(obj,indent=2))
print('PASS: exact Routh r2..40; independent complex counts r29/r30; imaginary-axis exclusion; simple roots; compound graph irreducibility')

# Independent elementary phase/modulus certificate for the finite range30..37.
# atan(u) >= u-u^3/3+u^5/5-u^7/7 and log(1+v) <= v-v^2/2+v^3/3.
from fractions import Fraction as F
b=F(228,25)
log2_lower=sum((F(2,(2*k+1)*3**(2*k+1)) for k in range(8)),F(0))
phase_cert=[]
for r in range(30,38):
    phase=F(0);logmod=F(0)
    for j in range(r,2*r):
        u=b/j;v=u*u
        phase+=u-u**3/3+u**5/5-u**7/7
        logmod+=(v-v**2/2+v**3/3)/2
    pg=phase-F(44,7);mg=log2_lower-logmod
    assert pg>F(1,200) and mg>F(1,1000)
    phase_cert.append({'r':r,'b':'228/25',
      'phase_lower_minus_44_over_7':str(pg),
      'log2_lower_minus_logmod_upper':str(mg)})
(ROOT/'rational_phase_certificates_30_37.json').write_text(json.dumps(phase_cert,indent=2))
print('PASS: elementary rational phase/modulus certificates r30..37')
