#!/usr/bin/env python3
"""Exact arithmetic companion to the sparse p-adic root-count manuscript.
No p-adic floating point, no numerical root finder.  Python 3.10+; SymPy only
for the optional squarefree-witness checks (included in the default run).
"""
from fractions import Fraction as F
from math import comb, gcd, lcm, prod
from itertools import combinations_with_replacement
import json, argparse, random
from pathlib import Path


def digits(n,p):
    s=0
    while n: s+=n%p; n//=p
    return s


def modulus(p,t):
    if t<=1: return 1
    D=max(digits(i,p) for i in range(t))
    A=(D-1+p-2)//(p-1)
    return p**A


def canonical(p,E):
    m=modulus(p,len(E)); count={}; out=[]
    for n in sorted(E):
        c=n%m; j=count.get(c,0); count[c]=j+1; out.append(c+j*m)
    return sorted(out)


def vp(x,p):
    if not x: return None  # +infinity
    x=F(x); a=abs(x.numerator); b=x.denominator; v=0
    while a%p==0: a//=p; v+=1
    while b%p==0: b//=p; v-=1
    return v


def inv(M):
    n=len(M); A=[[F(x) for x in row]+[F(i==j) for j in range(n)] for i,row in enumerate(M)]
    for j in range(n):
        k=next(k for k in range(j,n) if A[k][j]); A[j],A[k]=A[k],A[j]
        u=A[j][j]; A[j]=[x/u for x in A[j]]
        for k in range(n):
            if k!=j and A[k][j]:
                u=A[k][j]; A[k]=[x-u*y for x,y in zip(A[k],A[j])]
    return [row[n:] for row in A]


def optimum(p,E,r=None,compress=True,return_basis=False):
    """Largest index in any minimum-determinant Taylor row basis.
    r=None evaluates the open disk, via an explicit small rational delta.
    compress=False provides a separate test on the original support.
    """
    E=sorted(E); assert len(E)==len(set(E)) and min(E)>=0
    if compress: E=canonical(p,E)
    t=len(E); m=max(E)
    if t==1: return (0,[],E,r) if return_basis else 0
    if r is None: r=F(1,p-1)+F(1,2*(p-1)*t*(m+1))
    else: r=F(r)
    assert r>F(1,p-1)
    rows=[[comb(n,j) if n>=j else 0 for n in E] for j in range(m+1)]
    B=list(range(t)); C=inv(rows[:t])
    def coords(j):
        return [sum((a*C[k][i] for k,a in enumerate(rows[j]) if a),F(0)) for i in range(t)]
    def vals(j,a):
        return [(vp(x,p)+r*(j-B[i]),i) for i,x in enumerate(a) if x]
    for j in range(t,m+1):
        a=coords(j); v=vals(j,a)
        if not v: continue
        z,i=min(v)
        if z<0:
            ci=[C[k][i]/a[i] for k in range(t)]
            for k in range(t):
                for u in range(t):
                    C[k][u]=ci[k] if u==i else C[k][u]-a[u]*ci[k]
            B[i]=j
    active=[]
    for j in range(m+1):
        v=vals(j,coords(j))
        if v:
            z,i=min(v); assert z>=0
            if z==0: active.append(j)
    ans=max(active)
    return (ans,B,E,r) if return_basis else ans


def universal(p,t,r=None):
    """Finite exhaustive search over residue multisets; exponential in t."""
    m=modulus(p,t); best=-1; witness=None; count=0
    for residues in combinations_with_replacement(range(m),t):
        # canonicalization expects distinct actual exponents
        E=[c+i*m for i,c in enumerate(residues)]
        x=optimum(p,E,r); count+=1
        if x>best: best=x; witness=canonical(p,E)
    return dict(p=p,t=t,modulus=m,maximum=best,support=witness,profiles=count)


def poly_mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c


def witness(p,h):
    """Construct explicit integral polynomial from the two-residue functional."""
    assert 1<=h<p
    E=sorted([p*j for j in range(p+h)]+[1+p*j for j in range(h)])
    t=len(E); K=p*p+h-1
    moments=[((comb(j,h-1) if j>=h-1 else 0)-(j==h-1)-h*(j==h)-(j==p+h-1))%p for j in range(t)]
    assert moments[0]==0
    # L applied to each Lagrange cardinal polynomial on E.
    cs=[]
    for n in E:
        a=[1]; den=1
        for e in E:
            if e!=n: a=poly_mul(a,[-e,1]); den*=n-e
        cs.append(F(sum(x*y for x,y in zip(a,moments)),den))
    for j,M in enumerate(moments): assert sum(c*n**j for n,c in zip(E,cs))==M
    den=lcm(*(x.denominator for x in cs)); cs=[int(x*den) for x in cs]
    common=gcd(*cs); cs=[c//common for c in cs]
    r=F(1,p-1)+F(1,2*(p-1)*K)
    def root_count(cs):
        vals=[]
        for j in range(max(E)+1):
            a=sum(c*comb(n,j) for n,c in zip(E,cs) if n>=j)
            if a: vals.append((vp(a,p)+r*j,j))
        mu=min(x[0] for x in vals)
        return max(j for v,j in vals if v==mu),mu
    N,mu=root_count(cs); assert N==K,(p,h,N,K)
    # A small perturbation fills any zero coefficients and makes roots simple.
    precision=max(1,mu.numerator//mu.denominator+1); step=p**precision
    cs=[c if c else step for c in cs]
    import sympy as sp
    x=sp.Symbol('X')
    for tries in range(max(E)+2):
        poly=sp.Poly.from_dict({(n,):c for n,c in zip(E,cs)},x,domain=sp.ZZ)
        if all(cs) and sp.gcd(poly,poly.diff()).degree()==0: break
        cs[0]+=step
    else: raise AssertionError('squarefree perturbation not found')
    N2,mu2=root_count(cs); assert (N2,mu2)==(N,mu)
    return dict(p=p,h=h,t=t,maximum=K,depth=str(r),degree=max(E),minimum_weight=str(mu),
                terms=[[n,str(c)] for n,c in zip(E,cs)],squarefree=True,perturbation_trials=tries)


def run(out):
    results={'method':'Exact rational basis exchanges; integer Taylor coefficients and exact polynomial gcd.', 'universal':[], 'witnesses':[], 'rigidity':[]}
    for p,ts in [(2,range(2,10)),(3,range(2,9))]:
        for t in ts:
            row=universal(p,t); results['universal'].append(row)
            if p+2<=t<=2*p+1: assert row['maximum']==p*p+(t-p)//2-1,row
            print('universal',row,flush=True)
    for p in [2,3,5,7,11,13,17,19]:
        for h in sorted({1,min(2,(p+1)//2,p-1),(p+1)//2 if p>2 else 1}):
            row=witness(p,h); results['witnesses'].append(row)
            # An independent determinant-basis calculation on selected small supports.
            if p<=7:
                assert optimum(p,[n for n,c in row['terms']])==row['maximum']
            print('witness',p,h,row['maximum'],flush=True)
    # Same residue data, different original exponents, same exact optimum at a range of depths.
    rng=random.Random(20261127)
    for p,t in [(2,6),(2,8),(3,5),(3,7),(5,8),(5,11)]:
        for _ in range(3):
            E=sorted(rng.sample(range(0,3*t),t)); m=modulus(p,t); E2=sorted(e+i*m for i,e in enumerate(E))
            for r in [None,F(1,p-1)+F(1,20),F(1,p-1)+F(1,3),F(2)]:
                a=optimum(p,E,r,compress=False); b=optimum(p,E2,r,compress=False); c=optimum(p,E,r)
                assert a==b==c,(p,t,E,E2,r,a,b,c)
                results['rigidity'].append(dict(p=p,t=t,E=E,E2=E2,r=str(r),maximum=a))
        print('rigidity',p,t,'OK',flush=True)
    out.write_text(json.dumps(results,indent=2)+'\n')
    print(f'PASS: {len(results["universal"])} exhaustive profile searches, {len(results["witnesses"])} squarefree witnesses, {len(results["rigidity"])} rigidity checks',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('certificates.json'))
    parser.add_argument('--universal',nargs=2,type=int,metavar=('P','T'))
    parser.add_argument('--support',nargs='+',type=int,metavar='N',help='prime followed by distinct exponents')
    parser.add_argument('--depth',type=F,default=None,help='rational closed depth; omitted = open disk')
    args=parser.parse_args()
    if args.universal: print(json.dumps(universal(*args.universal,args.depth),indent=2))
    elif args.support: print(optimum(args.support[0],args.support[1:],args.depth))
    else: run(args.output)
