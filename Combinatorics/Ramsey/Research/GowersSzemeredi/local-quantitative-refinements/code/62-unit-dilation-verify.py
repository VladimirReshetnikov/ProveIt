#!/usr/bin/env python3
"""Exact checks for Unit-Dilation Restriction on Cyclic Groups.

Only Python's standard library is required. These finite checks supplement,
but do not replace, the proofs in the manuscript. Run from any directory.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product, combinations
from math import gcd, log10, log, lcm
from pathlib import Path
import argparse, json, random, sys, time

@lru_cache(None)
def factor(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError('positive integer required')
    out, p = [], 2
    while p*p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p; e += 1
            out.append((p,e))
        p += 1 if p == 2 else 2
    if n > 1: out.append((n,1))
    return tuple(out)

@lru_cache(None)
def phi(n: int) -> int:
    out = n
    for p,_ in factor(n): out = out//p*(p-1)
    return out

@lru_cache(None)
def mu(n: int) -> int:
    fs = factor(n)
    return 0 if any(e>1 for _,e in fs) else (-1)**len(fs)

@lru_cache(None)
def divisors(n: int) -> tuple[int, ...]:
    ds=[1]
    for p,e in factor(n): ds=[d*p**j for d in ds for j in range(e+1)]
    return tuple(sorted(ds))

def ramanujan(q: int, n: int) -> int:
    t=q//gcd(q,n)
    return mu(t)*(phi(q)//phi(t))

def coefficients(L: int) -> tuple[tuple[int,int], ...]:
    if L<2: raise ValueError('L must be at least two')
    return tuple((c,L-abs(c)) for c in range(1-L,L))

@lru_cache(None)
def profile(m: int,L: int,q: int) -> F:
    # q=1 is the respected-tuple enhancement A_{m,L}.
    numer=phi(q)*L**m+2*sum((L-c)**m*ramanujan(q,c) for c in range(1,L))
    return F(numer,phi(q)*L**m)

def all_scalar_profile(m: int,L: int,q: int) -> F:
    return F(L**m+2*sum((L-c)**m for c in range(q,L,q)),L**m)

@lru_cache(None)
def residue_powers(m: int,L: int,d: int) -> int:
    counts=defaultdict(int)
    for c,u in coefficients(L):counts[c%d]+=u
    return sum(u**m for u in counts.values())

@lru_cache(None)
def prop_numer(m: int,L: int) -> int:
    return sum(u**m for _,u in coefficients(L))

@lru_cache(None)
def kappa(m: int,L: int,N: int|None=None) -> F:
    # Exact maximal obstruction if N is None, otherwise exact modulus profile.
    ds=range(1,2*L-1) if N is None else (d for d in divisors(N) if d<2*L-1)
    v=sum(phi(d)*(residue_powers(m,L,d)-prop_numer(m,L)) for d in ds)
    return F(v,L**(2*m))

def kappa_bound(m: int) -> F:
    if m<4:raise ValueError('m must be at least four')
    return 1+F(5,4)**(m-1)*F(1,2**(m-2))*(1+F(2,m-3))+F(1,2**(m-4))

def check_profiles() -> dict:
    count=0
    for m in (4,6,8,16):
        for L in range(2,33):
            A=profile(m,L,1)
            assert A>=F(2*L,m+1)
            for q in range(2,161):
                B=profile(m,L,q)
                assert 0<=B<=F(q,phi(q)), (m,L,q,B)
                if q>=L**3:assert B<4
                if L & (L-1)==0:
                    assert B<=1+3*(L.bit_length()-1)
                count+=1
    # Exact formula for all-scalar averaging at order two defects.
    regression=[]
    for L in (8,32,128,512):
        A=profile(16,L,1); full=all_scalar_profile(16,L,2); unit=profile(16,L,2)
        regression.append({'L':L,'A':float(A),'all_scalar_bad':float(full),
                           'unit_bad':float(unit),'all_scalar_gain':float(A/full),
                           'unit_gain':float(A/unit)})
    return {'exact_profile_cases':count,'order_two_regression':regression}

def check_gcd() -> dict:
    count=0
    table=[]
    maxima=[]
    for m in (4,6,8,16):
        K=kappa_bound(m)
        for L in range(2,41):
            kap=kappa(m,L)
            assert 0<=kap<=K
            for N in (2,3,4,6,8,9,12,16,25,30,60,101,210,2310):
                assert 0<=kappa(m,L,N)<=kap
                count+=1
        best_L=max(range(2,41),key=lambda L:kappa(m,L))
        maxima.append({"m":m,"tested_L_range":[2,40],"maximizing_L":best_L,
                       "maximum":str(kappa(m,best_L))})
        for L in (2,3,4,8,16,32):
            table.append({'m':m,'L':L,'kappa':str(kappa(m,L)),
                          'decimal':float(kappa(m,L))})
        assert kappa(m,2)==1-F(1,4**(m-1))
        assert kappa(m,3)==1+F(5**m+4**m+2*3**m-6*2**m-12,9**m)
    assert kappa_bound(16)<F(1003,1000)
    assert kappa(16,3)>1+F(1,2**14)*(1+F(2,13))
    # Independent enumeration verifies the divisor formula, not just its bound.
    enum_count=0
    for L in (2,3):
        coeff=coefficients(L)
        for N in range(2,13):
            num=0
            for tup in product(coeff,repeat=4):
                cs=[x[0] for x in tup]
                # Signs absorbed using the symmetry of triangular weights.
                if len(set(cs))==1:continue
                g=N
                for c in cs[:-1]:g=gcd(g,c-cs[-1])
                w=1
                for _,u in tup:w*=u
                num+=w*g
            assert F(num,L**8)==kappa(4,L,N)
            enum_count+=1
    return {'weighted_modulus_cases':count,'independent_coefficient_enumerations':enum_count,
            'K16':str(kappa_bound(16)),'K16_decimal':float(kappa_bound(16)),
            'kappa_table':table,'finite_range_maxima':maxima}

def joint_probability(points: tuple[int,...],N: int,M: int,L: int,f: tuple[int,...]) -> F:
    # Fourier expansion of the product over points. Repeated inputs are allowed.
    d={(0,0):1}
    for x in points:
        nd=defaultdict(int)
        for (a,b),v in d.items():
            for c,u in coefficients(L):
                nd[((a+c*x)%N,(b+c*f[x])%M)]+=u*v
        d=nd
    num=sum(v*ramanujan(M,b) for (a,b),v in d.items() if a==0)
    return F(num,phi(M)*L**(2*len(points)))

def check_rounding() -> dict:
    rng=random.Random(20261006)
    records=[]
    for N,M,L in ((3,2,2),(4,4,3),(5,6,2),(6,4,3),(6,6,4),(7,8,2)):
        f=tuple(rng.randrange(M) for _ in range(N))
        subsets=[tuple(i for i in range(N) if mask>>i&1) for mask in range(1<<N)]
        J={s:joint_probability(s,N,M,L,f) for s in subsets}
        assert all(0<=v<=1 for v in J.values())
        # Mobius inversion gives exact probabilities of the random selected set.
        P={}
        for s in subsets:
            ss=set(s)
            P[s]=sum(((-1)**(len(t)-len(s))*J[t] for t in subsets if ss<=set(t)),F(0))
        assert all(v>=0 for v in P.values())
        assert sum(P.values())==1
        counts={s:[0,0] for s in subsets}
        G0=Y0=0; EG=EY=F(0); WG=WY=F(0); repeated=0
        badorders=Counter(); cache={}
        for x0,x1,x2 in product(range(N),repeat=3):
            x3=(x0+x1-x2)%N; t=(x0,x1,x2,x3)
            defect=(f[x0]+f[x1]-f[x2]-f[x3])%M
            good=defect==0
            s=tuple(sorted(set(t))); tm=tuple(sorted(t))
            if tm not in cache:cache[tm]=joint_probability(tm,N,M,L,f)
            v=cache[tm]
            if good:G0+=1; EG+=J[s]; WG+=v
            else:
                Y0+=1; EY+=J[s]; WY+=v
                badorders[M//gcd(M,defect)]+=1
            repeated+=len(s)<4
            for sub in subsets:
                if set(s)<=set(sub):counts[sub][0 if good else 1]+=1
        mainG=profile(4,L,1)*G0/L**4
        mainY=sum((profile(4,L,q)*n for q,n in badorders.items()),F(0))/L**4
        error=kappa(4,L,N)*N**2
        assert abs(WG-mainG)<=error
        assert abs(WY-mainY)<=error
        assert EG>=WG and EY<=WY+repeated
        assert repeated<=6*N**2
        assert sum(P[s]*counts[s][0] for s in subsets)==EG
        assert sum(P[s]*counts[s][1] for s in subsets)==EY
        eta=F(1,4)
        obj=eta*EG-(1-eta)*EY
        assert max(eta*g-(1-eta)*b for g,b in counts.values())>=obj
        records.append({'N':N,'M':M,'L':L,'map':f,'respected':G0,'bad':Y0,
                        'expected_respected':str(EG),'expected_bad':str(EY),
                        'weighted_good_error':str(WG-mainG),
                        'weighted_bad_error':str(WY-mainY),
                        'error_bound':str(error),'repeated_tuples':repeated,
                        'exact_subset_probabilities_checked':len(subsets)})
    return {'rounding_cases':records,
            'total_subset_outcomes':sum(r['exact_subset_probabilities_checked'] for r in records)}

def log_fraction(x: F) -> float:
    return log10(x.numerator)-log10(x.denominator)

def parameters(alpha: F, eta: F, beta: F) -> dict:
    x=alpha*eta; e=1
    while F(2**e)<34*(1+3*e)/x:e+=1
    L=2**e
    assert L<=2*(136/x)**2
    retention=alpha/F(17*L**15)
    threshold=F(4148*L**15)/(x*beta**15)
    coarse_retention=F(1,2**245)*alpha**31*eta**30
    coarse_threshold=F(2**253)/(x**31*beta**15)
    assert retention>=coarse_retention
    assert threshold<=coarse_threshold
    assert retention>=(x/4)**(2**19)
    return {'alpha':str(alpha),'eta':str(eta),'beta':str(beta),'e':e,'L':L,
            'log10_retention':log_fraction(retention),'log10_N_threshold':log_fraction(threshold),
            'log10_original_retention':(2**19)*log_fraction(x/4)}

def check_parameters() -> dict:
    table=[parameters(F(1,a),F(1,e),F(1,2)) for a,e in ((2,2),(10,10),(100,100))]
    for a in (1,2,3,10,100):
        for e in (1,2,3,10,100):parameters(F(1,a),F(1,e),F(1,3))
    return {'parameter_table':table,'parameter_cases':28}

def check_primorial() -> dict:
    q=1; records=[]
    for p in (2,3,5,7,11,13):
        q*=p
        if q<30:continue
        L=q//6
        B=profile(16,L,q); A=profile(16,L,1)
        # Lower bound obtained from the two primitive residues +1 and -1.
        lower=A/phi(q)
        assert B>=lower
        records.append({'q':q,'L':L,'q_over_phi':str(F(q,phi(q))),
                        'primitive_profile':float(B),'proven_lower':float(lower)})
    return {'primorial_cases':records}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args=ap.parse_args(); start=time.monotonic()
    out={'status':'PASS','arithmetic':'fractions.Fraction and integer arithmetic; decimal displays only are rounded',
         'seed':20261006,'python':sys.version.split()[0]}
    for check in (check_profiles,check_gcd,check_rounding,check_parameters,check_primorial):out.update(check())
    out['elapsed_seconds']=round(time.monotonic()-start,3)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS:',args.output)
    print('Exact profile cases:',out['exact_profile_cases'])
    print('Weighted modulus cases:',out['weighted_modulus_cases'])
    print('K16:',out['K16_decimal'])
    print(json.dumps(out['parameter_table'],indent=2))
    print('Elapsed:',out['elapsed_seconds'],'seconds')
if __name__=='__main__':main()
