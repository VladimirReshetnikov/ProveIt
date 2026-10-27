#!/usr/bin/env python3
"""Bounded exact three-term A90 coefficient regrouping; no candidate materialization.
Uses only stdlib and the pinned frozen certificate as inert JSON data.
Search is deliberately incomplete and capped at 30000 polynomial subproblems.
"""
from pathlib import Path
from functools import lru_cache
from itertools import combinations,product
from math import gcd
import hashlib,json,resource,time
resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
START=time.monotonic()
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'thirteen-second-first-norm-corrections/CERTIFICATE.json'
PIN='b05205f7a5e40dcddf78d77fd6a170a79c4e0df45c3ba23c9bc8b68c3f44d3e5'
def require(b,m):
    if not b:raise ValueError(m)
raw=PARENT.read_bytes();require(hashlib.sha256(raw).hexdigest()==PIN,'parent pin')
prior=json.loads(raw)
# Independent cuts Z=bG, T,V,F2=f²,h=f²-1,C,R,X. Parent V² is already paid.
NAMES=('Z','T','V','F2','h','C','R','X'); zero=(0,)*8
KEEP=12

def leaf(s):return ('leaf',s)
def const(c):return ('const',c)
def binary(op,a,b):
    if op in ('*','+') and repr(b)<repr(a):a,b=b,a
    return (op,a,b)
def times(a,b):
    if a==const(1):return b
    if b==const(1):return a
    return binary('*',a,b)
@lru_cache(None)
def gates(e):
    if e[0] in ('leaf','const'):return frozenset()
    return gates(e[1])|gates(e[2])|{e}
def cost(e):return len(gates(e))+1 # Z=bG is always one new paid operation.
def power(i,n):
    if n==0:return const(1)
    if i==2 and n==2:return leaf('V2')
    if n==1:return leaf(NAMES[i])
    if n%2==0:
        a=power(i,n//2);return times(a,a)
    return times(leaf(NAMES[i]),power(i,n-1))
def monomial(m,c=1):
    factors=[power(i,n)for i,n in enumerate(m)if n]
    if c!=1:factors.append(const(c))
    if not factors:return const(1)
    # This fixed monomial-factor ordering is an intentional search restriction.
    expr=factors[0]
    for f in factors[1:]:expr=times(expr,f)
    return expr

def key(p):return tuple(sorted((m,c)for m,c in p.items()if c))
def selected(items):
    d={e:None for e in items}
    return tuple(sorted(d,key=lambda e:(cost(e),len(repr(e)),repr(e)))[:KEEP])
def combine(op,aa,bb):return [binary(op,a,b)for a,b in product(aa,bb)]

@lru_cache(None)
def solve(k):
    require(time.monotonic()-START<45,'45-second exploratory cap')
    require(solve.cache_info().misses<=30000,'bounded subproblem cap')
    p=dict(k)
    if len(p)==1:
        (m,c),=p.items();return (monomial(m,c),)
    answers=[]
    # Factoring all common monomial powers and coefficient gcd is optional.
    g=0
    for c in p.values():g=gcd(g,abs(c))
    common=tuple(min(m[i]for m in p)for i in range(8))
    if g>1 or any(common):
        q={tuple(x-y for x,y in zip(m,common)):c//g for m,c in p.items()}
        factor=monomial(common,g)
        answers.extend(times(factor,e)for e in solve(key(q)))
    # Every unordered partition is an exact sum, enabling common factors
    # within smaller groups. Signs stay explicit integer coefficients.
    ks=list(p);first=ks[0]
    for n in range(1,len(ks)):
        for tail in combinations(ks[1:],n-1):
            left={first,*tail};right=set(ks)-left
            if not right:continue
            a={m:p[m]for m in left};b={m:p[m]for m in right}
            answers.extend(combine('+',solve(key(a)),solve(key(b))))
            # Paid subtraction may avoid a separate multiplication by -1.
            answers.extend(combine('-',solve(key(a)),solve(key({m:-c for m,c in b.items()}))))
            answers.extend(combine('-',solve(key(b)),solve(key({m:-c for m,c in a.items()}))))
    # A variable Horner split factors every divisible monomial together.
    for i in range(8):
        for n in sorted({m[i]for m in p if m[i]>0}):
            a={m:c for m,c in p.items()if m[i]>=n}
            b={m:c for m,c in p.items()if m[i]<n}
            if not b:continue
            q={tuple(x-n if j==i else x for j,x in enumerate(m)):c for m,c in a.items()}
            aa=[times(power(i,n),e)for e in solve(key(q))]
            answers.extend(combine('+',aa,solve(key(b))))
    return selected(answers)

# Exact A90's three monomials; no unknown identities are assumed in search.
def term(c,**kw):return tuple(kw.get(n,0)for n in NAMES),c
p=dict([term(16,Z=2,T=2,V=2,h=1),term(32,Z=1,T=2,V=2,F2=1,C=1),
        term(-32,Z=2,T=2,V=1,F2=2,R=1)])

# Full small cut-polynomial evaluation validates every retained expression.
def add(a,b,k=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+k*c
    return {m:c for m,c in r.items()if c}
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            z=tuple(x+y for x,y in zip(m,n));r[z]=r.get(z,0)+c*d
    return {m:c for m,c in r.items()if c}
@lru_cache(None)
def evaluate(e):
    if e[0]=='const':return {zero:e[1]}
    if e[0]=='leaf':
        m=list(zero)
        if e[1]=='V2':m[2]=2
        else:m[NAMES.index(e[1])]=1
        return {tuple(m):1}
    a,b=evaluate(e[1]),evaluate(e[2])
    return mul(a,b)if e[0]=='*'else add(a,b,1 if e[0]=='+'else-1)
answers=solve(key(p))
for e in answers:require(evaluate(e)==p,'complete coefficient identity')
out={'scope':'Incomplete bounded exact A90 regrouping over independent cuts; no candidate files',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'parent_sha256':PIN,
 'subproblems':solve.cache_info().misses,'retained_per_subproblem':KEEP,
 'best':[{'new_coefficient_operations':cost(e),'total_sphere_operations':75+3+cost(e),
          'expression':e,'full_cut_polynomial_terms':len(evaluate(e))}for e in answers]}
print(json.dumps(out,indent=2))
