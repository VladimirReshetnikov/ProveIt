from functools import lru_cache
from collections import Counter
import sympy as s
from quartic import compositions,mzv

@lru_cache(None)
def shuffle(a,b):
    if not a:return {b:1}
    if not b:return {a:1}
    out=Counter()
    for t,c in shuffle(a[1:],b).items():out[(a[0],)+t]+=c
    for t,c in shuffle(a,b[1:]).items():out[(b[0],)+t]+=c
    return dict(out)

@lru_cache(None)
def stuffle(a,b):
    if not a:return {b:1}
    if not b:return {a:1}
    out=Counter()
    for t,c in stuffle(a[1:],b).items():out[(a[0],)+t]+=c
    for t,c in stuffle(a,b[1:]).items():out[(b[0],)+t]+=c
    for t,c in stuffle(a[1:],b[1:]).items():out[(a[0]+b[0],)+t]+=c
    return dict(out)

def word(a):return sum(((0,)*(x-1)+(1,) for x in a),())
def ind(w):
    a=[];n=1
    for c in w:
        if c==0:n+=1
        else:a.append(n);n=1
    assert n==1
    return tuple(a)

def sha(a,b):
    return {ind(w):c for w,c in shuffle(word(a),word(b)).items()}

Z2,Z3,Z5,Z7=s.symbols('zeta2 zeta3 zeta5 zeta7')
seed={(2,):Z2,(3,):Z3,(4,):s.Rational(2,5)*Z2**2,(5,):Z5,(6,):s.Rational(8,35)*Z2**3,(7,):Z7}

def generate(maxw=7):
    reduced={():s.S.One}
    allinds={w:[cs for cs in compositions(w) if cs[0]>=2] for w in range(2,maxw+1)}
    reports=[]
    for w in range(2,maxw+1):
        inds=allinds[w]
        syms=[mzv(i) for i in inds]
        eqs=[]
        # Add shuffle and stuffle product evaluations at lower total weights.
        for a in range(2,w-1):
            b=w-a
            for ia in allinds.get(a,[]):
                for ib in allinds.get(b,[]):
                    rhs=reduced[ia]*reduced[ib]
                    for maker in (sha,stuffle):
                        eqs.append(sum(c*mzv(i) for i,c in maker(ia,ib).items())-rhs)
        # Extended double shuffle with one divergent weight-one input.
        for iv in allinds.get(w-1,[]):
            row=Counter(sha((1,),iv))
            row.subtract(stuffle((1,),iv))
            assert all(not c or i[0]>=2 for i,c in row.items())
            eqs.append(sum(c*mzv(i) for i,c in row.items() if c))
        # Ordinary duality.
        for iv in inds:
            dual=ind(tuple(1-c for c in reversed(word(iv))))
            eqs.append(mzv(iv)-mzv(dual))
        if (w,) in seed:eqs.append(mzv((w,))-seed[w,])
        sol=s.linsolve(eqs,syms)
        assert len(sol)==1
        vals=list(sol)[0]
        leftover=set().union(*(e.free_symbols for e in vals))-set((Z2,Z3,Z5,Z7))
        assert not leftover,(w,leftover)
        reduced.update({i:s.expand(e) for i,e in zip(inds,vals)})
        reports.append((w,len(inds),len(eqs)))
    return reduced,reports

if __name__=='__main__':
    red,reports=generate()
    print(reports)
    from quartic import coordinate,centered
    subs={mzv(i):e for i,e in red.items() if i}
    for j in range(8):print('D',j,s.expand(coordinate(4,2*j+1).subs(subs)))
    for r in range(6):print('V',r,s.expand(centered(4,2*r).subs(subs)))
