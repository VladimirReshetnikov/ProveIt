#!/usr/bin/env python3
"""Reproduce exact certificates and independently cross-check the implementation.

Run from any directory: python code/verify.py
Requires SymPy for symbolic identities; all graph counting uses only Python's
standard library. Outputs are written to ../data and ../tex.
"""
from __future__ import annotations
import json
import math
from itertools import combinations
from pathlib import Path
import platform
import random
import sys
import time
from fractions import Fraction
import sympy as sp
from support_count import (brute_force, hall_coefficients, hall_graph,
                           maximum_matching_cover, support_polynomial, ulc_margins)
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT/'data'; TEX = ROOT/'tex'
DATA.mkdir(exist_ok=True); TEX.mkdir(exist_ok=True)
messages=[]
def report(text):
    print(text, flush=True); messages.append(text)
def dump(name,obj):
    (DATA/name).write_text(json.dumps(obj,indent=2)+'\n')
def first_failure(alpha,beta,gamma):
    assert alpha<0 and beta>0 and gamma>0
    def q(w): return alpha*w*w+beta*w+gamma
    hi=1
    while q(hi)>=0: hi*=2
    lo=0
    while hi-lo>1:
        mid=(lo+hi)//2
        if q(mid)<0: hi=mid
        else: lo=mid
    assert q(hi)<0<=q(hi-1)
    return hi
def check_first_identity(graph, right_size, u, v, coeff):
    if len(coeff) < 3:
        return
    u = [Fraction(1)]*len(graph) if u is None else list(map(Fraction,u))
    v = [Fraction(1)]*right_size if v is None else list(map(Fraction,v))
    _,_,cx,cy = maximum_matching_cover(graph,right_size)
    cover=[(0,x) for x in cx]+[(1,y) for y in cy]
    index={vertex:i for i,vertex in enumerate(cover)}
    r=len(cover); W=[Fraction(0)]*r; edges=[]
    for x,row in enumerate(graph):
        for y in row:
            group=index[(0,x)] if (0,x) in index else index[(1,y)]
            weight=u[x]*v[y]
            W[group]+=weight
            edges.append((x,y,group,weight))
    K=sum((e[3]*f[3] for e,f in combinations(edges,2)
           if e[2]!=f[2] and (e[0]==f[0] or e[1]==f[1])),Fraction(0))
    B4=Fraction(0)
    for I in combinations(range(len(graph)),2):
        for J in combinations(range(right_size),2):
            if all(y in graph[x] for x in I for y in J):
                B4+=u[I[0]]*u[I[1]]*v[J[0]]*v[J[1]]
    rhs=sum(((a-b)**2 for a,b in combinations(W,2)),Fraction(0))/(2*r)+K+B4
    lhs=Fraction(r-1,2*r)*coeff[1]**2-coeff[2]
    assert lhs==rhs and lhs>=0

start=time.perf_counter()
report('Exact verification for Hall Bottlenecks and the Limits of Rank Normalization')
report(f'Python {platform.python_version()}; SymPy {sp.__version__}')
for bits in range(512):
    graph=[[j for j in range(3) if bits>>(3*i+j)&1] for i in range(3)]
    for u,v in [(None,None),([2,3,5],[7,11,13])]:
        coeff0=support_polynomial(graph,3,u,v)
        assert coeff0==brute_force(graph,3,u,v)
        check_first_identity(graph,3,u,v,coeff0)
report('PASS: all 512 labelled 3-by-3 graphs, unit weights and one positive unequal weight vector (1024 exact comparisons).')
rng=random.Random(782120)
for _ in range(200):
    m=rng.randrange(1,7); n0=rng.randrange(1,7)
    graph=[[j for j in range(n0) if rng.random()<.35] for i in range(m)]
    u=[Fraction(rng.randrange(1,8),rng.randrange(1,8)) for i in range(m)]
    v=[Fraction(rng.randrange(1,8),rng.randrange(1,8)) for j in range(n0)]
    assert support_polynomial(graph,n0,u,v)==brute_force(graph,n0,u,v)
report('PASS: first-margin defect identity on all rank-at-least-two instances in the 3-by-3 test suite.')
report('PASS: 200 additional seeded graphs of shore sizes 1 through 6, positive rational weights (seed 782120).')
small=0
for s0 in range(1,4):
    for n0 in range(s0,5):
        for w0 in [Fraction(1,3),1,2,7]:
            weights=[1]*n0+[w0]*s0
            graph=hall_graph(s0,n0)
            expected=hall_coefficients(s0,n0,w0)
            assert support_polynomial(graph,n0+s0,weights,weights)==expected
            assert brute_force(graph,n0+s0,weights,weights)==expected
            small+=1
report(f'PASS: {small} small Hall-family instances agree under the closed formula, cover-type algorithm, and independent subset dynamic program.')
# The lead example uses exact integer arithmetic everywhere.
s0,n0,w0=4,11,500
graph=hall_graph(s0,n0); weights=[1]*n0+[w0]*s0
coeff=hall_coefficients(s0,n0,w0)
assert coeff==support_polynomial(graph,n0+s0,weights,weights)
assert coeff==brute_force(graph,n0+s0,weights,weights)
ml,mr,cx,cy=maximum_matching_cover(graph,n0+s0)
assert len(cx)+len(cy)==8
rank_margins=ulc_margins(coeff,8); shore_margins=ulc_margins(coeff,15)
assert all(x>0 for x in rank_margins[:-1]) and rank_margins[-1]<0
assert all(x>=0 for x in shore_margins)
assert 7*coeff[7]**2-16*coeff[6]*coeff[8]==rank_margins[-1]
assert rank_margins[-1]==9*3025**2*w0**14*(-w0*w0+480*w0+2304)
assert -w0*w0+480*w0+2304==-7696
witness={'s':s0,'n':n0,'activity':w0,'vertices':30,'edges':104,'rank':8,
         'left_weights':weights,'right_weights':weights,'adjacency':graph,
         'coefficients':list(map(int,coeff)), 'rank_normalized_margins':list(map(int,rank_margins)),
         'shore_normalized_margins':list(map(int,shore_margins)),
         'minimum_cover_left':cx,'minimum_cover_right':cy,
         'matching_left_mates':ml,
         'last_margin_reduced_quadratic_value':-7696}
dump('rank8_witness.json',witness)
report('PASS: 30-vertex, 104-edge, rank-eight witness at w=500; formula, cover-type algorithm, and full independent support enumeration agree; last rank margin negative and all others positive.')
report('PASS: every order-15 margin of that witness is nonnegative.')
# Symbolic core-three coefficient formula and sign certificates.
n,w,x,j,s=sp.symbols('n w x j s', real=True)
def binom_poly(n,k):
    return sp.prod(n-i for i in range(k))/sp.factorial(k) if k>=0 else sp.Integer(0)
def symbolic_hall(s0):
    return [sp.expand(sum(sp.binomial(s0,i)*sp.binomial(s0,jj)
                          *binom_poly(n,k-i)*binom_poly(n,k-jj)*w**(i+jj)
                          for i in range(s0+1) for jj in range(s0+1)
                          if i+jj>=k and k>=i and k>=jj))
            for k in range(2*s0+1)]
a=symbolic_hall(3)
A=binom_poly(n,3);B=binom_poly(n,2)
explicit=[1,9*w*w+6*n*w,(6*B+9*n*n)*w*w+18*n*w**3+9*w**4,
          (2*A+18*n*B)*w**3+(6*B+9*n*n)*w**4+6*n*w**5+w**6,
          (6*n*A+9*B*B)*w**4+6*n*B*w**5+n*n*w**6,
          6*A*B*w**5+B*B*w**6,A*A*w**6]
assert all(sp.expand(u-v)==0 for u,v in zip(a,explicit))
margins=[sp.expand(k*(6-k)*a[k]**2-(k+1)*(7-k)*a[k-1]*a[k+1]) for k in range(1,6)]
Q=(-n*n+34*n-49)*w*w+12*(n-1)*(n-2)*(n+3)*w+8*(n-1)*(n-2)**2*(n+1)
assert sp.expand(margins[4]-n**4*(n-1)**2*w**10*Q/48)==0
factors=[9*w**2,3*w**4,w**6,w**8*n*n/4]
certificates=[]
tex=[]
for k in range(1,5):
    P=sp.cancel(margins[k-1]/factors[k-1])
    assert sp.denom(P)==1
    shifted=sp.Poly(sp.expand(P.subs(n,x+2)),w,x)
    assert all(c>0 for c in shifted.coeffs())
    # Group by w power. Each row gives coefficients in ascending x order.
    rows=[]
    for power in range(sp.degree(shifted.as_expr(),w)+1):
        px=sp.Poly(shifted.as_expr().coeff(w,power),x)
        if px.is_zero: continue
        coefficients=[int(px.nth(i)) for i in range(px.degree()+1)]
        assert all(c>=0 for c in coefficients)
        rows.append({'w_power':power,'x_coefficients_ascending':coefficients})
    certificates.append({'k':k,'positive_factor':str(factors[k-1]),'rows':rows})
    tex.append('\\begin{center}\n\\small\n\\begin{tabular}{r l}\n\\toprule\n'+
               '$w$ power & Coefficients in ascending powers of $x$ \\\\\n\\midrule')
    for row in rows:
        tex.append(str(row['w_power'])+' & $'+r',\;'.join(map(str,row['x_coefficients_ascending']))+'$ \\\\')
    tex.append('\\bottomrule\n\\end{tabular}\n\\end{center}')
    tex.append('\\noindent Table for $P_'+str(k)+'(x,w)$.\n')
(TEX/'positivity_tables.tex').write_text('\n'.join(tex)+'\n')
dump('rank6_positive_certificates.json',certificates)
article=(ROOT/'article.tex').read_text()
embedded=article.split('%% BEGIN GENERATED POSITIVITY TABLES\n',1)[1].split('%% END GENERATED POSITIVITY TABLES',1)[0]
assert embedded.strip()==(TEX/'positivity_tables.tex').read_text().strip()
report('PASS: all seven symbolic rank-six coefficients, the exact final-margin factorization, and positive-coefficient certificates for the first four margins.')
unit=sp.Poly(sp.expand(Q.subs({n:x+3,w:1})),x)
assert all(c>0 for c in unit.all_coeffs())
report('PASS: every unit-weight member of the core-three family satisfies all rank-six inequalities.')
thresholds=[]
for n0 in [33,34,36,40,48,50,64,100]:
    aa=-n0*n0+34*n0-49
    bb=12*(n0-1)*(n0-2)*(n0+3)
    cc=8*(n0-1)*(n0-2)**2*(n0+1)
    wmin=first_failure(aa,bb,cc)
    thresholds.append({'n':n0,'vertices':2*(n0+3),'first_integer_failure':wmin,
                       'Q_at_failure':aa*wmin*wmin+bb*wmin+cc})
dump('rank6_thresholds.json',thresholds)
report('PASS: exact integer threshold table for the rank-six family.')
# General core size: tail formulas and endpoint threshold verified algebraically
# in independent indeterminates A,B,C and then against the combinatorial sums.
AA,BB,CC=sp.symbols('A B C')
z0=AA**2*w**(2*s)
z1=2*s*AA*BB*w**(2*s-1)+BB**2*w**(2*s)
z2=(s*(s-1)*AA*CC+s*s*BB**2)*w**(2*s-2)+2*s*BB*CC*w**(2*s-1)+CC**2*w**(2*s)
alpha=(2*s-1)*BB**4-4*s*AA**2*CC**2
beta=4*s*AA*BB*((2*s-1)*BB**2-2*s*AA*CC)
gamma=4*s*s*(s-1)*AA**2*(BB**2-AA*CC)
# Factor out the common power first, avoiding ambiguous symbolic power rules.
endpoint=(2*s-1)*(2*s*AA*BB+BB**2*w)**2-4*s*AA**2*(s*(s-1)*AA*CC+s*s*BB**2+2*s*BB*CC*w+CC**2*w*w)
assert sp.expand(endpoint-(alpha*w*w+beta*w+gamma))==0
for s0 in range(2,7):
    vals={s:s0,AA:binom_poly(n,s0),BB:binom_poly(n,s0-1),CC:binom_poly(n,s0-2)}
    seq=symbolic_hall(s0)
    assert all(sp.expand(g.subs(vals)-seq[2*s0-offset])==0 for offset,g in enumerate([z0,z1,z2]))
report('PASS: general endpoint identity in independent A,B,C,s; tail coefficients cross-checked for core sizes 2 through 6.')
endpoint_table=[]
for s0 in range(3,11):
    n0=s0
    def abc(s0,n0):
        A0=math.comb(n0,s0);B0=math.comb(n0,s0-1);C0=math.comb(n0,s0-2)
        return ((2*s0-1)*B0**4-4*s0*A0*A0*C0*C0,
                4*s0*A0*B0*((2*s0-1)*B0*B0-2*s0*A0*C0),
                4*s0*s0*(s0-1)*A0*A0*(B0*B0-A0*C0))
    while abc(s0,n0)[0]>=0: n0+=1
    abc0=abc(s0,n0);g=math.gcd(*abc0);prim=[z//g for z in abc0]
    first=first_failure(*prim)
    endpoint_table.append({'s':s0,'smallest_n_for_endpoint_failure':n0,
                           'vertices':2*(s0+n0),'first_integer_failure':first,
                           'primitive_quadratic_abc':prim})
dump('general_endpoint_thresholds.json',endpoint_table)
report('PASS: exact endpoint thresholds for core sizes 3 through 10, including the 30-vertex witness.')
# Limiting normalization: monotonicity numerator is coefficientwise positive.
N=j*j*(s+j+1);D=s*(2*j+1)+j*(j+1)
derivative=sp.Poly(sp.expand(sp.diff(N,j)*D-N*sp.diff(D,j)),j,s)
assert all(c>0 for c in derivative.coeffs())
critical=(8*s*s-11*s+4)/(3*s-2)
assert sp.factor((s+j+N/D).subs(j,s-1)-critical)==0
assert sp.factor(critical-(sp.Rational(8,3)*s-sp.Rational(17,9)+sp.Rational(2,9)/(3*s-2)))==0
report('PASS: limiting normalization monotonicity, exact critical order, and asymptotic division identities.')
# Defensive API tests, including the empty graph and invalid weights.
assert support_polynomial([],0)==[1]
assert support_polynomial([[],[]],3)==[1]
for args in [([[0]],1,[0],[1]), ([[1]],1,None,None), ([[0]],1,[1.5],[1])]:
    try: support_polynomial(*args)
    except ValueError: pass
    else: raise AssertionError('invalid input was accepted')
report('PASS: empty/isolate cases and invalid-index/weight rejection.')
report('All checks passed. These are exact arithmetic and symbolic checks, not proof-assistant verification.')
report(f'Elapsed seconds on this run: {time.perf_counter()-start:.3f}')
(DATA/'verification_results.txt').write_text('\n'.join(messages)+'\n')
