"""Independent SymPy replay of all degree-one column certificates.

No imports from either discovery or standard-library replay code. Variables
are deliberately ordered n,p,q,e,d; neighborhood supports are constructed
as sets of distinct slot assignments.
"""
import hashlib,json
from pathlib import Path
from itertools import combinations_with_replacement
from functools import cache
import sympy as s

ROOT=Path(__file__).resolve().parent.parent
raw=(ROOT/'data'/'degree_one_certificate.json').read_bytes(); data=json.loads(raw)
n,p,q,e,d=s.symbols('n p q e d');vs=(n,p,q,e,d)
mu=n-e;h=p-d
G=[n-4,p-2*n+3,q-n+2,3*q-2*p,e,mu-2,d,q-2*d,
   e*(e-1)-2*d,h-e*mu,e*mu+mu*(mu-1)/2-h,h-n+1,q-mu*d,
   2*p*p-3*n*q,n*(n-1)-2*p,
   2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,
   2*e*p*p-3*e*n*q-2*n*d*d,2*h*h-3*q*mu,
   6*mu*d+3*e*mu*(mu-1)+mu*(mu-1)*(mu-2)-6*q]
K={1:q+2*p+n-d,2:q+2*p+n-d,4:q+2*h+mu,
   3:2*q+3*p+n-d,5:2*q+3*p+n-2*d,
   6:2*q+3*p+n-2*d,7:3*q+3*p+n-d}
C0=q+3*p+3*n+1-2*d-e
sets={m:{j for j in range(3) if m&(1<<j)} for m in range(1,8)}
def supports(a,b):return {frozenset((x,y)) for x in sets[a] for y in sets[b] if x!=y}
expected={pair for pair in combinations_with_replacement(range(1,8),2) if supports(*pair)}
@cache
def product(power):
    return s.Poly(s.prod(g**k for g,k in zip(G,power)),*vs,domain=s.QQ)
seen=set();terms=0
for record in data['certificates']:
    pair=tuple(record['masks'])
    if pair in seen:raise RuntimeError(('duplicate pair',pair))
    seen.add(pair)
    if record['margin']!=1:raise RuntimeError(('bad strict remainder',pair))
    sup=supports(*pair); rho=int(frozenset((0,1)) in sup)
    lam=q*len(sup)+p-d*(1-rho)
    target=s.Poly((n-2)*(16*K[pair[0]]*K[pair[1]]-15*C0*lam),*vs,domain=s.QQ)
    rebuilt=s.Poly(1,*vs,domain=s.QQ)
    for term in record['terms']:
        power=tuple(term['powers']);weight=s.Rational(term['weight'])
        if len(power)!=20 or any(type(x)!=int or x<0 for x in power):raise RuntimeError(('bad exponent',pair,power))
        if weight<=0:raise RuntimeError(('nonpositive stored coefficient',pair,weight))
        rebuilt+=weight*product(power);terms+=1
    if target!=rebuilt:raise RuntimeError(('identity mismatch',pair,target-rebuilt))
if seen!=expected:raise RuntimeError(('pair coverage',seen^expected))
result={'certificate_sha256':hashlib.sha256(raw).hexdigest(),
        'independent_pairs':len(seen),'strictly_positive_terms':terms,
        'all_exact_identities_pass':True,'variable_order':['n','p','q','e','d']}
(Path(__file__).with_suffix('.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
