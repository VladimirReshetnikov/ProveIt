#!/usr/bin/env python3
"""Exact finite group checks. No third-party dependencies; Python >=3.10."""
import json
from collections import Counter, deque
from pathlib import Path
from fractions import Fraction

# irreducible F2 polynomials x^r + lower terms
MODULI = {2:0b111, 3:0b1011, 4:0b10011}

def model(r):
    q = 1 << r; poly=MODULI[r]; inf=q
    def mul(a,b):
        out=0
        while b:
            if b&1: out ^= a
            b >>= 1; a <<= 1
            if a&q: a ^= poly
        return out
    m=[[mul(a,b) for b in range(q)] for a in range(q)]
    inv=[0]+[next(b for b in range(1,q) if m[a][b]==1) for a in range(1,q)]
    def perm(a,b,c,d):
        out=[]
        for x in range(q):
            den=m[c][x]^d; num=m[a][x]^b
            out.append(m[num][inv[den]] if den else inf)
        out.append(m[a][inv[c]] if c else inf)
        return tuple(out)
    e=tuple(range(q+1))
    G=[e]+[perm(a,b,c,d) for a in range(q) for c in range(q) if a or c
            for b in (range(q) if a else [inv[c]])
            for d in ([m[inv[a]][1^m[b][c]]] if a else range(q))
            if (a,b,c,d)!=(1,0,0,1)]
    assert len(G)==len(set(G))==q*(q*q-1)
    def comp(a,b): return tuple(a[i] for i in b)
    def pinv(a):
        out=[0]*len(a)
        for i,j in enumerate(a): out[j]=i
        return tuple(out)
    def order(g):
        t=e; k=0
        while True:
            k+=1; t=comp(t,g)
            if t==e: return k
    def fix(g): return sum(i==j for i,j in enumerate(g))
    B={g for g in G if g[inf]==inf}; T={g for g in B if g[0]==0}
    U={perm(1,b,0,1):(-1 if b&1 else 1) for b in range(q)}
    assert set(U)<=B and len(B)==q*(q-1) and len(T)==q-1 and len(U)==q
    gen=next(g for g in G if fix(g)==0 and order(g)==q+1)
    Tp={e}; g=gen
    while g!=e: Tp.add(g);g=comp(g,gen)
    inverses={g:pinv(g) for g in G}
    def conj(g,h): return comp(comp(g,h),inverses[g])
    Np={g for g in G if conj(g,gen) in Tp}
    N={g for g in G if {g[0],g[inf]}=={0,inf}}
    assert len(Tp)==q+1 and len(Np)==2*(q+1) and len(N)==2*(q-1)
    # Conjugacy class enumeration and induced characters, via class intersections.
    unvisited=set(G); results=[]; lookup={}; rep={}
    while unvisited:
        h=min(unvisited); C={conj(g,h) for g in G}; unvisited-=C
        cent=len(G)//len(C)
        def ind(H, char=lambda h:1):
            return Fraction(cent*sum(char(k) for k in C.intersection(H)),len(H))
        St=fix(h)-1; P=(ind(U)-ind(B))/2
        D=ind(Np,lambda k:1 if k in Tp else -1)
        GG=ind(U,U.__getitem__); W=1+GG
        IT=ind(T); ITp=ind(Tp); IB=ind(B)
        assert GG==St+P+D and IT==1+2*St+P+D and ITp==1+P+D
        assert (len(G) if h==e else 0)==1+q*St+(q+1)*P+(q-1)*D
        assert IB==fix(h) and IT==fix(h)*(fix(h)-1)
        assert W==(q*q if h==e else 0 if fix(h)==1 else 1)
        assert all(x.denominator==1 for x in (P,D,GG,IT,ITp,W))
        typ='identity' if h==e else 'unipotent' if fix(h)==1 else 'split' if fix(h)==2 else 'nonsplit'
        vals=dict(type=typ,order=order(h),class_size=len(C),fixed=fix(h),St=St,P=int(P),D=int(D),GG=int(GG),W=int(W),PT=int(IT),PTprime=int(ITp))
        for k in C: lookup[k]=vals; rep[k]=h
        results.append(vals)
    assert len(results)==q+1
    assert sum(x['class_size']*x['GG']**2 for x in results)==q*len(G)
    assert sum(x['class_size']*x['W'] for x in results)==len(G)
    result={'q':q,'group_order':len(G),'conjugacy_classes':sorted(results,key=lambda x:(x['order'],x['type'],x['class_size'])),
            'type_counts':dict(Counter(lookup[g]['type'] for g in G))}
    # Independent exhaustive subgroup search for q=4,8, modulo conjugacy.
    if q<=8:
        ix={g:i for i,g in enumerate(G)}; n=len(G)
        mm=[[ix[comp(a,b)] for b in G] for a in G]
        ii=[ix[inverses[g]] for g in G]
        def generated(gs):
            H={0}; todo=[0]
            for a in todo:
                for b in gs:
                    t=mm[a][b]
                    if t not in H: H.add(t);todo.append(t)
            return frozenset(H)
        def orbit(H):
            return {frozenset(mm[mm[g][h]][ii[g]] for h in H) for g in range(n)}
        start=frozenset({0}); seen={start}; reps=[(start,())]
        for H,gs in reps:
            cosets=set(H)
            for g in range(n):
                if g in cosets: continue
                cosets.update(mm[h][g] for h in H)
                K=generated(gs+(g,))
                if K in seen: continue
                orb=orbit(K);seen.update(orb);reps.append((K,gs+(g,)))
        subgroup_rows=[]
        for H,gs in reps:
            st=Fraction(sum(lookup[G[h]]['St'] for h in H),len(H))
            d=Fraction(sum(lookup[G[h]]['D'] for h in H),len(H))
            assert st.denominator==d.denominator==1 and st>=0 and d>=0
            if len(H)>q-1: assert st==0 or d==0
            if len(H)>q+1: assert d==0
            subgroup_rows.append(dict(order=len(H),index=n//len(H),St_fixed=int(st),D_fixed=int(d),conjugates=len(orbit(H))))
        assert sum(x['conjugates'] for x in subgroup_rows)==len(seen)
        result['subgroup_search']={'conjugacy_class_count':len(reps),'subgroup_count':len(seen),'rows':sorted(subgroup_rows,key=lambda x:(x['order'],x['St_fixed'],x['D_fixed']))}
    return result

if __name__=='__main__':
    data=[model(r) for r in MODULI]
    path=Path(__file__).with_name('checks.json')
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    for x in data:
        print('q=',x['q'],'order=',x['group_order'],'classes=',len(x['conjugacy_classes']),
              'subgroups=',x.get('subgroup_search',{}).get('subgroup_count','not enumerated'))
    print('All exact assertions passed.')
