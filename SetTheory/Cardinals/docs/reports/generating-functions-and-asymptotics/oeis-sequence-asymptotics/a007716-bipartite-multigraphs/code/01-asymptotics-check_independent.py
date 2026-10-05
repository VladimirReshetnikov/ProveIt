#!/usr/bin/env python3
"""Independent finite audit. No producer imports; explicit failures survive -O."""
from fractions import Fraction as Q
from math import comb, factorial, gcd, prod
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json
import sympy as s

def require(ok, message):
    if not ok: raise RuntimeError(message)

def integer_parts(n, least=1):
    if n==0: yield ()
    for a in range(least,n+1):
        for tail in integer_parts(n-a,a): yield (a,)+tail

def block_partitions(n):
    if not n: yield (); return
    for part in block_partitions(n-1):
        bit=1<<(n-1)
        yield part+(bit,)
        for j in range(len(part)):
            yield part[:j]+(part[j]|bit,)+part[j+1:]

def class_den(lens):
    return prod(k**v*factorial(v) for k,v in Counter(lens).items())

def explicit_fixed(lens, partitions):
    n=sum(lens); perm=[]
    for a in lens:
        j=len(perm); perm.extend(list(range(j+1,j+a))+[j])
    image=[0]*(1<<n)
    for x in range(1,1<<n):
        bit=x&-x
        image[x]=image[x^bit]|(1<<perm[bit.bit_length()-1])
    return sum(all(image[b] in p for b in p) for p in partitions)

def cycle_formula(lens):
    c=len(lens)
    @lru_cache(None)
    def weight(mask):
        vals=[lens[j] for j in range(c) if mask>>j&1]
        g=gcd(*vals); h=len(vals)
        return sum(k**(h-1) for k in range(1,g+1) if g%k==0)
    @lru_cache(None)
    def count(mask):
        if not mask:return 1
        low=mask&-mask; rest=mask^low; sub=rest; total=0
        while True:
            group=sub|low
            total+=weight(group)*count(mask^group)
            if not sub: break
            sub=(sub-1)&rest
        return total
    return count((1<<c)-1)

def falling(n,a): return prod(n-j for j in range(a))
def rising(n,a): return prod(n+j for j in range(a))

N=10; bells=[]; rows=[]; checked=0
for n in range(N+1):
    ps=list(block_partitions(n)); bells.append(len(ps))
    aa=Q(0); zz=Q(0); mark=Q(0)
    for lens in integer_parts(n):
        c=len(lens); direct=explicit_fixed(lens,ps); formula=cycle_formula(lens)
        require(direct==formula, f'fixed partition mismatch {lens}')
        require(bells[c]<=direct<=2**(n-c)*bells[c],f'global bound {lens}')
        den=class_den(lens); aa+=Q(direct**2,den); zz+=Q(bells[c]**2,den)
        if lens.count(2): mark+=Q(2*lens.count(2)*bells[c]*bells[c-1],den)
        checked+=1
    # Independent labeled rectangular-matrix inclusion-exclusion, including empty n=0.
    mass=Q(int(n==0))
    for k in range(1,n+1):
        for l in range(1,n+1):
            matrices=0
            for i in range(1,k+1):
                for j in range(1,l+1):
                    matrices+=(-1)**(k+l-i-j)*comb(k,i)*comb(l,j)*comb(i*j+n-1,n)
            require(matrices>=0, 'negative matrix count')
            mass+=Q(matrices,factorial(k)*factorial(l))
    require(mass==zz, f'mass normalization mismatch n={n}')
    if n>=2:
        removed=sum((Q(bells[len(p)+1]*bells[len(p)],class_den(p)) for p in integer_parts(n-2)),Q(0))
        require(mark==removed, f'marked transposition identity n={n}')
    require(aa.denominator==1 and aa>=zz+mark, f'positivity n={n}')
    rows.append({'n':n,'a':int(aa),'Z':str(zz),'Y':str(mark),'a_minus_Z_minus_Y':str(aa-zz-mark)})

moments=[]
for n in range(2,11):
    T=Q(7,3)
    for spec in ({2:1},{3:1},{2:2},{2:1,3:1},{1:1,2:1}):
        support=sum(i*a for i,a in spec.items())
        if support>n:continue
        actual=Q(0)
        for p in integer_parts(n):
            cnt=Counter(p)
            actual+=Q(factorial(n),class_den(p))*T**len(p)*prod(falling(cnt[i],a) for i,a in spec.items())/rising(T,n)
        expected=falling(n,support)*T**sum(spec.values())/(prod(i**a for i,a in spec.items())*rising(T+n-support,support))
        require(actual==expected,f'Ewens moment n={n}, spec={spec}')
        moments.append({'n':n,'spec':str(spec),'moment':str(actual)})

w=s.symbols('w',positive=True)
v=w/(w+1); mean=w*w/(2*(w+1)**2)
mass_correction=s.factor(-w*w*mean+w*w*v+w**4*v/4-w*w/2-w**4/6)
combined=s.factor(mass_correction+w**3)
claimed=w*w*(w**4+11*w**3+22*w*w+12*w-6)/(12*(w+1)**2)
require(s.cancel(combined-claimed)==0,'first correction algebra')
result={'status':'PASS','max_n':N,'cycle_types_checked':checked,'rows':rows,'factorial_moments_checked':len(moments),'moments':moments,'formal_mass_correction':str(mass_correction),'formal_total_correction':str(combined),'scope':'Exact finite checks; first-correction symbolic calculation alone does not certify the asymptotic remainder.'}
path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('rows','moments')},indent=2))
