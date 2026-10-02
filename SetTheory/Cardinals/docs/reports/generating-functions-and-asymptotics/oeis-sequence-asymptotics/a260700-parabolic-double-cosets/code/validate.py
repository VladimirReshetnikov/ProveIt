#!/usr/bin/env python3
"""Recompute the exact source formula, check actual cosets, and test corrections."""
from pathlib import Path
from math import comb,factorial
from itertools import permutations
import argparse, json, sys, hashlib
import mpmath as mp
import sympy as sp

ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('limit',type=int,nargs='?',default=40)
parser.add_argument('--output-dir',type=Path,default=Path('replay-output'))
args=parser.parse_args();N=args.limit
if not 5<=N<=400: parser.error('limit must be between 5 and 400 (reference data range)')
OUT=args.output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
fac=[factorial(n) for n in range(N+1)]
S1=[[0]*(N+1) for _ in range(N+1)]
S2=[[0]*(N+1) for _ in range(N+1)]
S1[0][0]=S2[0][0]=1
for n in range(1,N+1):
    for k in range(1,n+1):
        S1[n][k]=S1[n-1][k-1]+(n-1)*S1[n-1][k]
        S2[n][k]=S2[n-1][k-1]+k*S2[n-1][k]
f=[[sum(fac[l]*S2[n-j][l-j] for l in range(j,n+1)) for j in range(n+1)] for n in range(N+1)]
g=[[sum(comb(c,j)*f[n][j]*f[n][c-j] for j in range(c+1)) for c in range(n+1)] for n in range(N+1)]
T=[[0]*(N//2+1) for _ in range(N//2+1)]
T[0][0]=1
for m in range(1,N//2+1):
    for c in range(1,m+1): T[m][c]=T[m-1][c-1]+c*c*T[m-1][c]
q=[]; p=[]
for n in range(N+1):
    v=0
    for m in range(n//2+1):
        for c in range(m+1):
            h=(-1)**c*fac[2*c]*T[m][c]
            assert h%fac[c]==0
            v+=comb(n,2*m)*(h//fac[c])*g[n-2*m+c][c]
    q.append(v)
    pn=sum(S1[n][m]*q[m] for m in range(n+1))
    assert pn%fac[n]==0
    p.append(pn//fac[n])
    assert 0<=q[n]<=f[n][0]**2

known={}
for line in (ROOT/'data/b260700.txt').read_text().splitlines():
    if line.strip() and not line.startswith('#'):
        a,b=line.split(); known[int(a)]=int(b)
assert all(p[n]==known[n] for n in range(1,N+1))

def brute_cosets(n):
    ps=list(permutations(range(n))); ids={p:i for i,p in enumerate(ps)}
    left=[]; right=[]
    for i in range(n-1):
        left.append([ids[tuple(i+1 if a==i else i if a==i+1 else a for a in p)] for p in ps])
        row=[]
        for p in ps:
            v=list(p); v[i],v[i+1]=v[i+1],v[i]; row.append(ids[tuple(v)])
        right.append(row)
    out=set()
    for I in range(1<<(n-1)):
        for J in range(1<<(n-1)):
            maps=[left[i] for i in range(n-1) if I>>i&1]+[right[i] for i in range(n-1) if J>>i&1]
            unseen=set(range(len(ps)))
            while unseen:
                x=unseen.pop(); todo=[x]; component={x}
                while todo:
                    x=todo.pop()
                    for mapping in maps:
                        y=mapping[x]
                        if y not in component:
                            component.add(y); unseen.remove(y); todo.append(y)
                out.add(frozenset(component))
    return len(out)
brute={n:brute_cosets(n) for n in range(1,6)}
assert all(p[n]==v for n,v in brute.items())

mp.mp.dps=90
r=mp.log(2); K=mp.exp(-r*r/2)/(4*r*r)
co=json.loads((ROOT/'data/coefficients-order4.json').read_text())
symr=sp.Symbol('r')
B=[mp.mpf(str(sp.N(sp.sympify(x).subs(symr,sp.log(2)),90))) for x in co['B']]
D=[mp.mpf(str(sp.N(sp.sympify(x).subs(symr,sp.log(2)),90))) for x in co['D']]
rows=[]
for n in [25,50,100,200,400]:
    rat=mp.mpf(known[n])*r**(2*n)/mp.factorial(n)/K
    residuals=[mp.mpf(n)**(m+1)*(rat-sum(B[i]/mp.mpf(n)**i for i in range(m+1))) for m in range(4)]
    rows.append({'n':n,'scaled_residuals_after_orders_0_to_3':[mp.nstr(v,45) for v in residuals]})
qrows=[]
for n in [n for n in [25,50,100] if n<=N]:
    rat=mp.mpf(q[n])*4*r**(2*n+2)/mp.factorial(n)**2*mp.exp(r*r)
    qrows.append({'n':n,'scaled_residuals':[mp.nstr(mp.mpf(n)**(m+1)*(rat-sum(D[i]/mp.mpf(n)**i for i in range(m+1))),45) for m in range(4)]})

# Verify the exact cycle-configuration formula independently for n<=40.
def cycle_configs(k,l=2):
    if k==0: yield {}
    elif l-1<=k:
        for a in range(k//(l-1)+1):
            for tail in cycle_configs(k-a*(l-1),l+1):
                yield ({l:a} if a else {})|tail
cyclechecks=0
for n in range(1,min(40,N)+1):
    for k in range(min(7,n)):
        total=0
        for cfg in cycle_configs(k):
            support=sum(l*a for l,a in cfg.items())
            if support>n:continue
            den=fac[n-support]
            for l,a in cfg.items():den*=l**a*fac[a]
            total+=fac[n]//den
        assert total==S1[n][n-k]
        cyclechecks+=1

report={'exact_formula_matches_OEIS_through':N,'brute_group_coset_counts':brute,
        'cycle_identity_checks':cyclechecks,
        'B':[mp.nstr(v,65) for v in B], 'D':[mp.nstr(v,65) for v in D],
        'K':mp.nstr(K,65),'c':mp.nstr(-K*B[1],65),'log_c':mp.nstr(mp.log(-K*B[1]),65),
        'p_residuals':rows,'q_residuals':qrows,
        'bfile_sha256':hashlib.sha256((ROOT/'data/b260700.txt').read_bytes()).hexdigest()}
(OUT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
(OUT/'exact-values.json').write_text(json.dumps({'p':list(map(str,p)),'q':list(map(str,q))},indent=2)+'\n')
print(json.dumps(report,indent=2))
