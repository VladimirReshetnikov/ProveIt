#!/usr/bin/env python3
"""Optional LP-based discovery of certificates. Verification does not need this script.
Requires NumPy, SciPy and SymPy. Recreates the search settings used for each
reported degree; numerical solver variations may select different supports.
Writes generated_certN.json, leaving the delivered certificates untouched.
"""
import itertools, math, collections, sys, json, functools
from fractions import Fraction as F
from scipy.optimize import linprog
import numpy as np
from sympy import mobius, ZZ
from sympy.polys.matrices import DomainMatrix
from sympy import Matrix
from pathlib import Path

@functools.lru_cache(None)
def parts(n,lo=1):
    if n==0:return ((),)
    return tuple((k,)+q for k in range(lo,n+1) for q in parts(n-k,k))
def z(p):
    return math.prod(k**v*math.factorial(v) for k,v in collections.Counter(p).items())
def add(a,b):return tuple(sorted(a+b))
def conv(a,b):
    r=collections.defaultdict(int)
    for p,x in a.items():
        for q,y in b.items():r[add(p,q)]+=x*y
    return {p:v for p,v in r.items() if v}
def cyc_type(p):
    n=len(p); seen=set(); lengths=[]
    for i in range(n):
        if i in seen:continue
        j=i;k=0
        while j not in seen:seen.add(j);k+=1;j=p[j]
        lengths.append(k)
    return tuple(sorted(lengths))
@functools.lru_cache(None)
def ram(d,k):return sum(a*int(mobius(d//a)) for a in range(1,d+1) if d%a==0 and k%a==0)
@functools.lru_cache(None)
def block(m):
    out={}
    def put(desc,row):
        row={k:v for k,v in row.items() if v};
        # normalize integer gcd
        g=math.gcd(*row.values());row={k:v//g for k,v in row.items()}; key=tuple(sorted(row.items()))
        out.setdefault(key,(desc,row))
    for e in range(2 if m>=2 else 1):
        put(('S',m,e),{p:(-1)**(e*(m-len(p)))*math.factorial(m)//z(p) for p in parts(m)})
    for d in range(1,m+1):
        if m%d:continue
        row=collections.defaultdict(int)
        for j in range(m):
            g=math.gcd(j,m);row[(m//g,)*g]+=ram(d,j)
        put(('C',m,d),row)
    if m>=3:
        for a in range(2):
            if a and m%2:continue
            for b in range(2):
                row=collections.defaultdict(int)
                for j in range(m):
                    g=math.gcd(j,m);row[(m//g,)*g]+=(-1)**(a*j)
                    p=cyc_type(tuple((j-i)%m for i in range(m)));row[p]+=(-1)**(a*j+b)
                put(('D',m,a,b),row)
    # Affine normalizer of a cycle (C_m semidirect cyclic subgroup of units)
    for u in range(2,m):
        if math.gcd(u,m)!=1:continue
        us=[1];v=u
        while v!=1:us.append(v);v=v*u%m
        order=len(us)
        for d in range(1,order+1):
            if order%d:continue
            row=collections.defaultdict(int)
            for j,v in enumerate(us):
                for a in range(m):row[cyc_type(tuple((v*i+a)%m for i in range(m)))]+=ram(d,j)
            put(('A',m,u,d),row)
    return tuple(out.values())

@functools.lru_cache(None)
def rows(n):
    res={}
    # product of transitive blocks, dedup. Avoid storing all huge intermediates except final
    for p in parts(n):
        # same size blocks sorted
        groups=[]
        for m,c in collections.Counter(p).items():groups.append(list(itertools.combinations_with_replacement(block(m),c)))
        for choices in itertools.product(*groups):
            bs=tuple(x for y in choices for x in y)
            sums=[sum(row.values()) for desc,row in bs]
            zero=[i for i,s in enumerate(sums) if s==0]
            if not zero:continue
            if len(zero)==1 and sum(v*k.count(1) for k,v in bs[zero[0]][1].items()):continue
            row={():1}
            for desc,r in bs:row=conv(row,r)
            key=tuple(sorted(row.items()))
            res.setdefault(key,tuple(desc for desc,r in bs))
    return list(res.items())

def target(n):
    ps=parts(n); b=[F(1,z(p)) for p in ps]; b[0]+=F(n-3,2); b[1]-=F(n-1,2);assert ps[1]==(1,)*(n-2)+(2,)
    return b

def solve(n):
    ps=parts(n); pp={p:i for i,p in enumerate(ps)};r=rows(n);print(n,'classes',len(ps),'rows',len(r),flush=True)
    # Normalize by identity coefficient and row-coordinate scale to moderate conditioning.
    A=np.zeros((len(ps),len(r)))
    for j,(k,d) in enumerate(r):
        rr=dict(k);t=rr[ps[0]]
        for p,v in k:A[pp[p],j]=v/t
    b=target(n); bb=np.array(list(map(float,b)))
    scale=np.array([min(1000000 if n>=16 else 10000,z(p)) for p in ps],float);scale[:2]=1
    # S_13 used the original full-system feasibility search.
    opts={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9}
    if n==13:
        sol=linprog(np.ones(len(r)),A_eq=A*scale[:,None],b_eq=bb*scale,bounds=(0,None),method='highs',options=opts)
    else:
        sol=linprog(np.random.default_rng(n+100 if n>=16 else n).random(len(r)),A_eq=(A*scale[:,None])[2:],b_eq=(bb*scale)[2:],bounds=(0,None),method='highs-ipm',options=opts)
    print(sol.message,flush=True)
    if not sol.success:return False
    jj=np.flatnonzero(sol.x>(1e-10 if n>=16 else 1e-11)); print('support',len(jj),'min',min(sol.x[jj]),'residual',max(abs(A@sol.x-bb)),flush=True)
    mat=Matrix([[dict(r[j][0]).get(p,0) for j in jj] for p in ps]); bv=Matrix(b)
    if n<16:
        x,params=mat.gauss_jordan_solve(bv)
        x=x.subs({p:0 for p in params})
    else:
        scale_den=math.factorial(n)
        dm=DomainMatrix.from_Matrix(mat).convert_to(ZZ)
        db=DomainMatrix.from_Matrix(bv*scale_den).convert_to(ZZ)
        xn,xd=dm.solve_den(db,method="rref")
        x=xn.to_Matrix()/(int(xd)*scale_den)
    if min(x)<0:print('negative exact',min(x));return False
    assert mat*x==bv
    cert={'n':n,'terms':[{'blocks':r[j][1],'weight':str(q)} for j,q in zip(jj,x) if q>0]}
    Path(__file__).with_name(f'generated_cert{n}.json').write_text(json.dumps(cert,indent=2)+'\n');print('EXACT OK',n,len(cert['terms']),flush=True);return True
if __name__=='__main__':
    if len(sys.argv)<2: raise SystemExit('usage: python search.py 13 [14 ...]')
    ok=True
    for n in map(int,sys.argv[1:]):
        try: ok=solve(n) and ok
        except Exception as e:
            print(type(e).__name__,e,flush=True); ok=False
    sys.exit(0 if ok else 1)
