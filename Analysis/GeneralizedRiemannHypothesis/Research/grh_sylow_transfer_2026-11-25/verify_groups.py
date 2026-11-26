#!/usr/bin/env python3
"""Exact finite group certificates. No external packages required."""
from itertools import permutations, product
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import gcd, lcm
import json

def compose(a,b): return tuple(a[i] for i in b)
def order(g, mul, ident):
    x=ident; n=0
    while True:
        x=mul(x,g); n+=1
        if x==ident: return n

def closure(gens,mul,ident):
    S={ident}; stack=[ident]
    while stack:
        x=stack.pop()
        for g in gens:
            y=mul(x,g)
            if y not in S: S.add(y); stack.append(y)
    return S

def cycle_type(g):
    seen=set(); C=[]
    for i in range(len(g)):
        if i not in seen:
            j=i; n=0
            while j not in seen: seen.add(j); n+=1; j=g[j]
            C.append(n)
    return tuple(sorted(C))

def fixed_count(g,H,G,mul,inv):
    n=sum(mul(mul(inv[x],g),x) in H for x in G)
    assert n%len(H)==0
    return n//len(H)

def verify_symmetric(n,gens):
    G=list(permutations(range(n))); ident=tuple(range(n)); inv={x:tuple(x.index(i) for i in range(n)) for x in G}
    Hs=[closure(g,compose,ident) for g in gens]
    assert all(all((n-len(cycle_type(g)))%2==0 for g in H) for H in Hs)
    ans=defaultdict(set)
    for g in G:
        ans[cycle_type(g)].add(len(Hs)*len(G)*(g==ident)-sum(fixed_count(g,H,G,compose,inv) for H in Hs))
    assert all(len(s)==1 for s in ans.values())
    weights={k:next(iter(v)) for k,v in ans.items()}
    assert sum(weights[cycle_type(g)] for g in G)==0
    divisor=gcd(*weights.values())
    return {'subgroup_orders':list(map(len,Hs)), 'weight_gcd':divisor,'weights':{','.join(map(str,k)):v//divisor for k,v in sorted(weights.items())}}

def cyc(n,*cycles):
    a=list(range(n))
    for c in cycles:
        for i,j in zip(c,c[1:]+c[:1]): a[i]=j
    return tuple(a)

# GL(3,2) realized as permutations of the seven nonzero binary vectors.
def linear(cols,v):
    y=0
    for i in range(3):
        if (v>>i)&1: y^=cols[i]
    return y

def glperm(cols):return tuple(linear(cols,v)-1 for v in range(1,8))
def gl_check():
    G=[glperm(c) for c in product(range(1,8),repeat=3) if len({linear(c,v) for v in range(8)})==8]
    assert len(G)==len(set(G))==168
    I=tuple(range(7)); inv={x:tuple(x.index(i) for i in range(7)) for x in G}; O={g:order(g,compose,I) for g in G}
    assert Counter(O.values())=={1:1,2:21,3:56,4:42,7:48}
    P=next(closure([r,s],compose,I) for r in G if O[r]==4 for s in G if O[s]==2 and compose(compose(s,r),s)==inv[r] and s not in closure([r],compose,I))
    assert len(P)==8
    r=next(g for g in P if O[g]==4); s=next(g for g in P if O[g]==2 and g not in closure([r],compose,I))
    def powr(i):
        g=I
        for _ in range(i):g=compose(g,r)
        return g
    lamA={compose(powr(i),I if j==0 else s):(-1)**j for i in range(4) for j in range(2)}
    lamB={compose(powr(i),I if j==0 else s):(-1)**i for i in range(4) for j in range(2)}
    assert set(lamA)==set(lamB)==P
    for L in [lamA,lamB]:
        assert all(L[compose(g,h)]==L[g]*L[h] for g in P for h in P)
    def induce(g,L):
        return Q(sum(L.get(compose(compose(inv[x],g),x),0) for x in G),len(P))
    vals=defaultdict(set)
    for g in G:vals[O[g]].add(induce(g,lamA)+induce(g,lamB))
    assert {k:next(iter(v)) for k,v in vals.items()}=={1:42,2:-2,3:0,4:0,7:0}
    assert all(len(v)==1 for v in vals.values())
    # Exact character calculations use pairs a+b sqrt(-7), rational a,b.
    # For all rows below the coefficients of the two order-7 classes agree,
    # so only the sum of the two character values is needed.
    chars=[(1,1,1,1,2),(3,-1,0,1,-1),(3,-1,0,1,-1),(6,2,0,0,-2),(7,-1,1,-1,0),(8,0,-1,0,2)]
    # subgroup inner products (order-7 totals multiplied by 3)
    def dot(coeff,d):
        z=[Q(sum(a*b for a,b in zip(c,coeff)),d) for c in chars]
        assert all(x.denominator==1 and x>=0 for x in z)
        return list(map(int,z))
    rows={
      'D8_lambda_A':dot((1,-3,0,2,0),8),
      'D8_lambda_B':dot((1,1,0,-2,0),8),
      'S4_trivial':dot((1,9,8,6,0),24),
      'S4_sign':dot((1,-3,8,-6,0),24),
      '7colon3_order3_char':dot((1,0,-7,0,3),21),
    }
    assert rows=={'D8_lambda_A':[0,1,1,0,1,1],'D8_lambda_B':[0,0,0,1,1,1],'S4_trivial':[1,0,0,1,0,0],'S4_sign':[0,0,0,0,1,0],'7colon3_order3_char':[0,0,0,0,0,1]}
    # Independently enumerate a point stabilizer S4 and a normalizer of C7.
    S4={g for g in G if g[0]==0}; C7=closure([next(g for g in G if O[g]==7)],compose,I)
    H={g for g in G if {compose(compose(g,h),inv[g]) for h in C7}==C7}
    assert len(S4)==24 and len(H)==21
    assert Counter(O[g] for g in S4)=={1:1,2:9,3:8,4:6}
    assert Counter(O[g] for g in H)=={1:1,3:14,7:6}
    # S4 acts faithfully on the four pairs {v, v+e1}, omitting {0,e1}:
    # use the natural action on the four 2D complements to the fixed line.
    # Compute signs via its action on the four Sylow 3-subgroups.
    sub3={frozenset(closure([g],compose,I)) for g in S4 if O[g]==3}; subs=list(sub3);assert len(subs)==4
    signs={}
    for g in S4:
        perm=tuple(subs.index(frozenset(compose(compose(g,h),inv[g]) for h in K)) for K in subs)
        signs[g]=(-1)**(4-len(cycle_type(perm)))
    assert {k:sum(signs[g] for g in S4 if O[g]==k) for k in (1,2,3,4)}=={1:1,2:-3,3:8,4:-6}
    return {'group_order':len(G),'order_counts':dict(sorted(Counter(O.values()).items())), 'induction_rows_columns':'1,3,3bar,6,7,8','induction_rows':rows,'combined_weight_by_order':{k:int(next(iter(v))) for k,v in sorted(vals.items())},'septic_cycle_types':{k:sorted(set(cycle_type(g) for g in G if O[g]==k)) for k in sorted(set(O.values()))}}

if __name__=='__main__':
    s4=verify_symmetric(4,[[cyc(4,(0,1),(2,3)),cyc(4,(0,2),(1,3))],[cyc(4,(0,1,2))]])
    s5=verify_symmetric(5,[[cyc(5,(0,1),(2,3)),cyc(5,(0,2),(1,3))],[cyc(5,(0,1,2))],[cyc(5,(0,1,2,3,4))]])
    assert s4['weights']=={'1,1,1,1':17,'1,1,2':0,'1,3':-1,'2,2':-3,'4':0}
    assert s5['weights']=={'1,1,1,1,1':133,'1,1,1,2':0,'1,1,3':-2,'1,2,2':-3,'1,4':0,'2,3':0,'5':-2}
    print(json.dumps({'S4':s4,'S5':s5,'PSL2(7)':gl_check()},indent=2))
