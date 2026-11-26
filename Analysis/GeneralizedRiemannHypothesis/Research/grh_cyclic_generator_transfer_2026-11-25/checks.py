#!/usr/bin/env python3
"""Exact finite checks for the cyclic-generator criterion. No analytic claims tested."""
from collections import Counter, deque
from fractions import Fraction
from math import factorial, gcd, prod
import csv, json
from pathlib import Path
HERE=Path(__file__).resolve().parent

def primes(n):
    return [p for p in range(2,n+1) if all(p%d for d in range(2,int(p**.5)+1))]
def partitions(n, lo=1):
    if n==0: yield ()
    for d in range(lo,n+1):
        for q in partitions(n-d,d): yield (d,)+q

def typ(x):
    seen=set(); out=[]
    for i in range(len(x)):
        if i in seen: continue
        j=i; k=0
        while j not in seen: seen.add(j); k+=1; j=x[j]
        out.append(k)
    return tuple(sorted(out))
def compose(a,b): return tuple(a[i] for i in b)
def size_generated(n, gens):
    e=tuple(range(n)); seen={e}; q=deque([e])
    while q:
        a=q.popleft()
        for b in gens:
            c=compose(a,b)
            if c not in seen: seen.add(c); q.append(c)
    return len(seen)
def rotation(n, start, p, j):
    a=list(range(n)); s=p**j
    for k in range(p):
        for i in range(s): a[start+k*s+i]=start+((k+1)%p)*s+i
    return tuple(a)
def sylow_gens(n,p):
    # Recursively split maximal p^a blocks; choose every local rotation.
    gs=[]; start=0; rem=n
    def rec(start, a):
        if a==0: return
        gs.append(rotation(n,start,p,a-1))
        for k in range(p): rec(start+k*p**(a-1),a-1)
    while rem:
        a=0
        while p**(a+1)<=rem: a+=1
        rec(start,a); start+=p**a; rem-=p**a
    return gs

def alt_sylow_gens(n,p):
    gs=sylow_gens(n,p)
    if p!=2:return gs
    bottom=[g for g in gs if typ(g).count(2)==1]
    upper=[g for g in gs if typ(g).count(2)!=1]
    return upper+[compose(bottom[0],g) for g in bottom[1:]] if bottom else upper

def vp_fact(n,p):
    r=0
    while n: n//=p; r+=n
    return r

def patterns(n):
    out=[]
    for p in primes(n):
        j=1 if p==2 else 0
        while p**(j+1)<=n:
            out.append((p,tuple([1]*(n-p**(j+1))+[p]*p**j)));j+=1
    return out

def centralizer(t): return prod(k**m*factorial(m) for k,m in Counter(t).items())
def weight_table(n):
    N=factorial(n); pats=patterns(n); w={tuple([1]*n):sum((Fraction(N*(p-1),p) for p,t in pats),Fraction())}
    for p,t in pats:w[t]= -Fraction((p-1)*centralizer(t),p)
    assert all(v.denominator==1 for v in w.values())
    divisor=gcd(*[int(v) for v in w.values()]) if w else 1
    divisor=max(divisor,1)
    return {t:int(v)//divisor for t,v in w.items()},divisor

def prime_power_type(t):
    # Nonidentity element of prime-power order iff all nontrivial cycle lengths are powers of one prime.
    non=[d for d in t if d>1]
    if not non:return False
    for p in primes(max(non)):
        if all(d in {p**j for j in range(1,max(non).bit_length()+1)} for d in non):return True
    return False

def irreducibility_certificate(poly,p):
    # exact Rabin irreducibility test via sympy finite-field gcd and modular powering
    import sympy as s
    x=poly.gen; n=poly.degree(); h=s.Poly(x,x,modulus=p); one=s.Poly(1,x,modulus=p)
    def powmod(a,k):
        r=one
        while k:
            if k&1:r=(r*a).rem(poly)
            k//=2;a=(a*a).rem(poly)
        return r
    assert powmod(h,p**n)==h.rem(poly)
    assert all(s.gcd(powmod(h,p**(n//q))-h,poly).degree()==0 for q in primes(n) if n%q==0)

def main():
    checked=[]
    for n in range(5,19):
        allowed={t for p,t in patterns(n)}
        for p in primes(n):
            gs=alt_sylow_gens(n,p)
            assert all(typ(g) in allowed for g in gs)
            assert all(compose(g,g)==tuple(range(n)) for g in gs) if p==2 else True
            expected=p**(vp_fact(n,p)-(p==2))
            observed=size_generated(n,gs) if expected<=20000 else None
            if observed is not None:assert observed==expected
            checked.append(dict(n=n,p=p,generators=len(gs),expected=expected,enumerated=observed))
    with (HERE/'sylow_checks.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=checked[0]);w.writeheader();w.writerows(checked)
    rows=[]
    for n in range(5,41):
        w,d=weight_table(n); N=factorial(n)
        assert sum(Fraction(v,centralizer(t)) for t,v in w.items())==0
        old=sum(1 for t in partitions(n) if (n-len(t))%2==0 and prime_power_type(t))
        rows.append(dict(n=n,cyclic_patterns=len(w)-1,sylow_patterns=old,normalization=d))
    with (HERE/'pattern_counts.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    w,d=weight_table(8)
    assert {t:v for t,v in w.items()}=={(1,)*8:22336,(1,)*4+(2,)*2:-16,(2,)*4:-32,(1,)*5+(3,):-40,(1,)*3+(5,):-4,(1,7):-1}
    import sympy as s, warnings
    warnings.filterwarnings('ignore',category=s.utilities.exceptions.SymPyDeprecationWarning)
    x=s.symbols('x'); pol=x**8-x-1; facs={}
    for p,desired in [(7,[8]),(19,[1,7]),(61,[1,2,5])]:
        f=s.Poly(pol,x,modulus=p); _, factors=f.factor_list(); assert all(e==1 for q,e in factors)
        assert sorted(q.degree() for q,e in factors)==desired
        assert prod((q for q,e in factors),start=s.Poly(1,x,modulus=p))==f
        for q,e in factors:irreducibility_certificate(q,p)
        facs[str(p)]=[str(q.as_expr()) for q,e in factors]
    cert={'sylow_cases':len(checked),'enumerated_cases':sum(r['enumerated'] is not None for r in checked),'pattern_count_rows':len(rows),'s8_weight_divisor':d,'s8_weights':{','.join(map(str,t)):v for t,v in w.items()},'factorizations':facs,'scope':'finite checks only; no numerical evidence for the analytic asymptotic'}
    (HERE/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps(cert,indent=2))
if __name__=='__main__':main()
