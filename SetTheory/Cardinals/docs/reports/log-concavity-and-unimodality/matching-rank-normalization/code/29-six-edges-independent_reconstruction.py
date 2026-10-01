"""Independent exact replay of the three six-edge cases.

Uses direct slot assignments and independently constructed generators. Does
not import either discovery program or any supplied replay implementation.
"""
from pathlib import Path
from itertools import combinations_with_replacement,product
from functools import cache
import json,hashlib
import sympy as S
ROOT=Path(__file__).resolve().parent.parent
slots={a:tuple(i for i in range(3) if a&(1<<i)) for a in range(1,8)}
def supports(a,b):return {frozenset((i,j)) for i in slots[a] for j in slots[b] if i!=j}
def basis(a,b,c):return any(len(set(t))==3 for t in product(slots[a],slots[b],slots[c]))
expected={x for x in combinations_with_replacement(range(1,8),2) if supports(*x)}

def run(mode):
    if mode=='triangular':
        n,p,q,e,f,d,g=S.symbols('n p q e f d g');vs=(n,p,q,e,f,d,g)
        u=p-d;v=d-g;mu=n-e;m=n-f;hp=p-g;X=2*p*p-3*n*q
        G=[n-4,p-2*n+3,q-n+2,3*q-2*p,e,mu-3,u-mu,d-e*mu,q-e*u,q+e*u-2*d,
           n*(n-1)-e*(e-1)-2*p,mu*(mu-1)-2*u,4*p*u*mu-2*n*u*u-3*q*mu*mu,X-2*d*d+4*e*q,
           mu*(mu-1)*(mu-2)+6*e*u-6*q,f-e,m-2,g-e*(f-e),f*(f-1)-e*(e-1)-2*g,
           hp-f*m,2*f*m+m*(m-1)-2*hp,q-m*g,6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,
           2*f*p*p-3*f*n*q-2*n*g*g,2*hp*hp-3*q*m,v-e*m,e*m+m*(m-1)/2-v,
           2*u*(2*hp-u)-3*q*m,X,2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,hp-n+1,g,v]
        c0=q+3*p-d-g+3*n-f-e+1
        profiles=[(u,7),(v,3),(g,1)]
        def singleton(a):return m+(f-e)*int(bool(a&6))+e*int(bool(a&4))
    elif mode=='star_edge':
        n,p,q,e,f,d,g=S.symbols('n p q e f d g');vs=(n,p,q,e,f,d,g)
        u=p-d;mu=n-e;m=n-f;hp=p-g;X=2*p*p-3*n*q
        G=[d,u,mu,n,p,q,m,hp,mu-f,n-4,p-2*n+3,q-n+2,3*q-2*p,e,mu-3,u-mu,d-e*mu,q-e*u,q+e*u-2*d,
           n*(n-1)-e*(e-1)-2*p,mu*(mu-1)-2*u,4*p*u*mu-2*n*u*u-3*q*mu*mu,X-2*d*d+4*e*q,
           mu*(mu-1)*(mu-2)+6*e*u-6*q,f,mu-f,m-2,g,f*(f-1)-2*g,
           hp-f*m,2*f*m+m*(m-1)-e*(e-1)-2*hp,q-m*g,
           6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,2*f*p*p-3*f*n*q-2*n*g*g,2*hp*hp-3*q*m,
           p-d-g,2*(p*p-d*d-g*g)-3*q*mu,hp-e*mu-f*(mu-f),q-e*u-(mu-f)*g,
           6*e*u+6*(mu-f)*g+3*f*(mu-f)*(mu-f-1)+(mu-f)*(mu-f-1)*(mu-f-2)-6*q,
           u-2*mu+4,hp-2*n+4,X,2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,hp-n+1]
        c0=q+3*p-d-g+3*n-2*e+1
        profiles=[(p-d-g,7),(d,3),(g,5)]
        def singleton(a):return mu+e*int(bool(a&4))
    else:
        n,p,q,f1,f2,g1,g2=S.symbols('n p q f1 f2 g1 g2');vs=(n,p,q,f1,f2,g1,g2)
        G=[n-4,p-2*n+3,q-n+2,3*q-2*p,2*p*p-3*n*q,n*(n-1)-2*p,
           2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q,p-g1-g2,2*(p*p-g1*g1-g2*g2)-3*n*q]
        for f,g in [(f1,g1),(f2,g2)]:
            m=n-f;h=p-g
            G.extend([f,m-2,g,f*(f-1)-2*g,h-f*m,2*f*m+m*(m-1)-2*h,q-m*g,
                      6*m*g+3*f*m*(m-1)+m*(m-1)*(m-2)-6*q,2*f*p*p-3*f*n*q-2*n*g*g,
                      2*h*h-3*q*m,h-n+1])
        c0=q+3*p-g1-2*g2+3*n-f2+1
        profiles=[(p-g1-g2,7),(g1,6),(g2,1)]
        def singleton(a):return n-f2+f2*int(bool(a&6))
    K={a:q*len(slots[a])+sum(w*len(supports(mask,a)) for w,mask in profiles)+singleton(a) for a in slots}
    @cache
    def monomial(power):return S.Poly(S.prod(g**k for g,k in zip(G,power)),*vs,domain=S.QQ)
    path=ROOT/'data'/f'find_{mode}_first.json';raw=path.read_bytes();data=json.loads(raw);seen=set();terms=0
    for rec in data['certificates']:
        pair=tuple(rec['masks'])
        if pair in seen:raise RuntimeError(('duplicate',mode,pair))
        seen.add(pair)
        if rec['margin']!=1:raise RuntimeError(('margin',mode,pair))
        lam=q*len(supports(*pair))+sum(w*int(basis(mask,*pair)) for w,mask in profiles)
        target=S.Poly((n-2)*(16*K[pair[0]]*K[pair[1]]-15*c0*lam),*vs,domain=S.QQ)
        rebuilt=S.Poly(1,*vs,domain=S.QQ)
        for term in rec['terms']:
            power=tuple(term['powers']);weight=S.Rational(term['weight'])
            if len(power)!=len(G) or any(type(k)!=int or k<0 for k in power) or weight<=0:
                raise RuntimeError(('invalid term',mode,pair))
            rebuilt+=weight*monomial(power);terms+=1
        if target!=rebuilt:raise RuntimeError(('identity',mode,pair,target-rebuilt))
    if seen!=expected:raise RuntimeError(('coverage',mode,seen^expected))
    return {'case':mode,'generators':len(G),'exact_identities':len(seen),'positive_terms':terms,
            'strict_remainder':1,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'all_passed':True}

results=[run(mode) for mode in ['triangular','star_edge','transpose']]
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
