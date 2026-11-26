"""Certified weights for all primitive nonreal Dirichlet characters below the
pair budget. Requires mpmath and sympy. Run as python nonreal.py > nonreal.json.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd, lcm
import json
from mpmath import iv
from sympy import divisors, factorint, mobius, primerange, primitive_root, totient

iv.dps = 32
SCALE = 2**34
PERIODS = 32


def scaled(x):
    """Round an interval to a dyadic approximation; certify its accuracy."""
    candidate = round(float(x.mid)*SCALE)
    assert abs(x*SCALE - candidate) < 1
    return candidate


@lru_cache(None)
def roots(m):
    rows = [(scaled(iv.cos(2*iv.pi*j/m)), scaled(iv.sin(2*iv.pi*j/m)))
            for j in range(m)]
    return tuple(x for x,y in rows),tuple(y for x,y in rows)


@lru_cache(None)
def inverse_weights(k):
    x=iv.mpf(k)
    return 1/x,iv.log(x)/x


def coefficients(q, residues):
    """For each residue, scaled approximations to its two finite-part sums."""
    n=q*PERIODS
    out=[]
    for r in residues:
        lvalue, logsum=iv.mpf(0),iv.mpf(0)
        for k in range(r,n,q):
            a,b=inverse_weights(k)
            lvalue+=a
            logsum+=b
        t=iv.mpf(n+r)
        logt=iv.log(t)
        lvalue+=-logt/q + 1/(2*t) + q/(12*t**2)
        logsum+=-logt**2/(2*q)+logt/(2*t)+q*(logt-1)/(12*t**2)
        out.append((scaled(lvalue),scaled(logsum)))
    return out


@lru_cache(None)
def log_table(p,e):
    modulus=p**e
    if p==2:
        base=5
        rank=max(1,modulus//4)
    else:
        base=int(primitive_root(p*p, smallest=True))
        rank=(p-1)*p**(e-1)
    row={}
    g=1
    for j in range(rank):
        row[g]=(0,j)
        if p==2:
            row[-g%modulus]=(1,j)
        g=g*base%modulus
    return row


def local_characters(p,e):
    if p==2:
        if e==1:
            return []
        if e==2:
            return [((-2,Fraction(1,2)),)]
        m=2**(e-2)
        return [((2,Fraction(j,m)),) + (((-2,Fraction(1,2)),) if neg else ())
                for j in range(1,m,2) for neg in (False,True)]
    m=(p-1)*p**(e-1)
    return [((p,Fraction(j,m)),) for j in range(1,m)
            if e==1 or j%p]


def enumerate_modulus(q):
    factors=list(factorint(q).items())
    options=[local_characters(p,e) for p,e in factors]
    if not all(options):
        return
    residues=[k for k in range(1,q) if gcd(k,q)==1]
    logs={}
    for p,e in factors:
        p,e=int(p),int(e)
        pairs=[log_table(p,e)[k%(p**e)] for k in residues]
        logs[p]=[v for _,v in pairs]
        if p==2:
            logs[-2]=[v for v,_ in pairs]
    coeff=coefficients(q,residues)
    w0,w1=map(tuple,zip(*coeff))
    # Scale error in the exact dot product from one unit of dyadic error
    # in either operand. Centers are integers, accumulated without overflow.
    def rounding_error(w):
        return iv.mpf(len(w)*(SCALE+1)+sum(map(abs,w)))/SCALE**2
    tail=1/(iv.mpf(60)*PERIODS**4)
    er0=rounding_error(w0)+tail
    er1=rounding_error(w1)+tail*iv.log((PERIODS+1)*q)
    sig_index=residues.index(q-1)
    zeros=[0]*len(residues)
    for choice in product(*options):
        key=tuple(sorted(key_entry for factor in choice for key_entry in factor))
        order=lcm(*(a.denominator for p,a in key))
        if order<=2:
            continue
        conjugate=tuple((p,1-a) for p,a in key)
        if key>conjugate:
            continue
        exps=zeros.copy()
        for p,a in key:
            mult=a.numerator*(order//a.denominator)
            exps=[h+mult*v for h,v in zip(exps,logs[p])]
        exps=[h%order for h in exps]
        conj_sign=exps[sig_index]
        assert 2*conj_sign%order==0
        cosine,sine=roots(order)
        re=[cosine[i] for i in exps]
        im=[sine[i] for i in exps]
        def component(w,angles,err):
            center=sum(v*a for v,a in zip(w,angles))
            return iv.mpf(center)/SCALE**2+iv.mpf([-1,1])*err
        L=iv.mpc(component(w0,re,er0),component(w0,im,er0))
        D=iv.mpc(component(w1,re,er1),component(w1,im,er1))
        val=iv.log(q/iv.pi)-iv.euler-2*(D/L).real
        if conj_sign==0:
            val-=2*iv.log(2)
        yield key,conjugate,val


def check_analytic_cutoff():
    upper = iv.mpf(0)
    for p in primerange(2,1001):
        k = p
        while k <= 1000:
            upper += iv.log(p)/k**2
            k *= p
    upper += (1+iv.log(1000))/1000
    assert upper < iv.mpf("0.6")
    assert (iv.log(400/iv.pi)-iv.euler-2*upper)/3 > 1


def character_count():
    def two_torsion(n):
        factors=factorint(n)
        e=factors.pop(2,0)
        return 2**len(factors)*(1 if e<=1 else 2 if e==2 else 4)
    return sum(int(mobius(q//d))*(int(totient(d))-two_torsion(d))
               for q in range(1,400) for d in divisors(q))


def certify():
    check_analytic_cutoff()
    Bq=2+iv.euler-iv.log(4*iv.pi)
    budget=(2-Bq)/2
    found=[]
    tested=0
    for q in range(3,400):
        for key,conj,value in enumerate_modulus(q):
            tested+=2
            assert value>0
            if value>budget:
                continue
            assert value<budget,(q,key,value)
            # Round endpoints outwards to units of 10^-9 and verify inclusion.
            from math import floor,ceil
            lo=floor(float(value.a)*1e9)-1
            hi=ceil(float(value.b)*1e9)+1
            assert iv.mpf(lo)/10**9 < value and iv.mpf(hi)/10**9 > value
            for char in [key,conj]:
                found.append({'q':q,'character':[[p,a.numerator,a.denominator] for p,a in char],
                              'B_lower':f'{lo//10**9}.{lo%10**9:09d}',
                              'B_upper':f'{hi//10**9}.{hi%10**9:09d}'})
    assert tested == character_count()
    return {'tested_nonreal_primitive_characters':tested,'characters':found}


if __name__=='__main__':
    print(json.dumps(certify(),indent=1))
