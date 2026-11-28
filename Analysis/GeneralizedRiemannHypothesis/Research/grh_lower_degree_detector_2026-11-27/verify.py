#!/usr/bin/env python3
"""Exact, independent class-count verification of detector identities.
No third-party packages. Does not test analytic RH or Lean proofs.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial, prod
import json


def mul(a,b):
    return tuple(a[b[i]] for i in range(len(a)))


def inv(a):
    return tuple(a.index(i) for i in range(len(a)))


def cycle(n,*cs):
    a=list(range(n))
    for c in cs:
        for i,j in zip(c,c[1:]+c[:1]): a[i]=j
    return tuple(a)


def ctype(p):
    seen=set(); sizes=[]
    for i in range(len(p)):
        if i in seen: continue
        j=i; z=0
        while j not in seen:
            seen.add(j); z+=1; j=p[j]
        sizes.append(z)
    return tuple(sorted(sizes,reverse=True))


def parity(p):
    return (-1)**(len(p)-len(ctype(p)))


def subgroup(n,*gens):
    e=tuple(range(n)); H={e}; queue=[e]
    for a in queue:
        for g in gens:
            b=mul(a,g)
            if b not in H:
                H.add(b); queue.append(b)
    return H


def induce(G,H,g,chi=lambda h:1):
    total=0
    for x in G:
        h=mul(mul(inv(x),g),x)
        if h in H: total+=chi(h)
    return Fraction(total,len(H))


def ind_data(G,subgroups,coeffs,regular_coeff):
    classes=Counter(ctype(g) for g in G)
    reps={ctype(g):g for g in G}
    out=[]
    for typ,g in sorted(reps.items()):
        rows=[induce(G,H,g,chi) for H,chi in subgroups]
        reg=len(G) if g==tuple(range(len(g))) else 0
        assert sum(c*x for c,x in zip(coeffs,rows))+regular_coeff*reg==0
        out.append({'type':typ,'size':classes[typ], 'induced_values':[int(x) for x in rows], 'regular':reg})
    # Check every group element, including both split A5 classes.
    for g in G:
        reg=len(G) if g==tuple(range(len(g))) else 0
        assert sum(c*induce(G,H,g,chi) for c,(H,chi) in zip(coeffs,subgroups))+regular_coeff*reg==0
    return out

one=lambda h:1
A5=[p for p in permutations(range(5)) if parity(p)==1]
c=cycle(5,(0,1,2)); d=cycle(5,(0,1),(3,4))
C=subgroup(5,c); P={p for p in A5 if p[4]==4}; D=subgroup(5,c,d)
assert (len(C),len(P),len(D))==(3,12,6)
assert C<=D and all(set(h[:3])=={0,1,2} for h in D)
sgnD=lambda h: parity(h[:3])
assert all(sgnD(mul(x,y))==sgnD(x)*sgnD(y) for x in D for y in D)
assert {h for h in D if sgnD(h)==1}==C
local=ind_data(A5,[(C,one),(P,one),(D,sgnD)],[5,-4,-2],-1)

A4=[p for p in permutations(range(4)) if parity(p)==1]; S4=list(permutations(range(4)))
V={p for p in A4 if ctype(p) in [(1,1,1,1),(2,2)]}
B=subgroup(4,cycle(4,(0,1),(2,3)))
assert len(V)==4 and all(mul(a,b) in V for a in V for b in V)
local2=ind_data(A4,[(B,one),(V,one)],[3,-2],-1)
C4=subgroup(4,cycle(4,(0,1,2)))
small=ind_data(S4,[(C4,one),(V,one),(set(A4),one)],[3,1,-3],-1)


def cent(t):
    return prod(k**m*factorial(m) for k,m in Counter(t).items())


def hist_H(r,delta=0):
    # Key records nontrivial cycle lengths only, and each entry counts elements.
    return Counter({(2,)* (2*e)+(3,)*j:comb(r,j)*2**j for e in range(delta+1) for j in range(r+1)})


def merge(a,b):
    return tuple(sorted(a+b))


def tensor_hist(a,b):
    out=Counter()
    for t,x in a.items():
        for u,y in b.items():out[merge(t,u)]+=x*y
    return out


def histogram(H,chi=one):
    out=Counter()
    for h in H:out[tuple(sorted(x for x in ctype(h) if x>1))]+=chi(h)
    return out


def check_identity(terms):
    # Each entry is (coefficient, subgroup order, signed class histogram).
    types=set().union(*(h.keys() for _,_,h in terms))
    for t in types:
        assert sum(Fraction(c*h[t],size) for c,size,h in terms)==0, (t,terms)
    return len(types)

P_hist=histogram(P); D_hist=histogram(D,sgnD); V_hist=histogram(V)
# Since every relevant class in A_n is unsplit, the same signed histograms
# certify both S_n and A_n induction identities (class-centralizer common factor).
rows=[]; checks=0
for n in range(5,61):
    r=(n-2)//3; delta=int(n-3*r==4)
    for j in range(1,r+1):
        prev=hist_H(j-1); order=3**(j-1)
        checks+=check_identity([(5,3*order,hist_H(j)),(-1,order,prev),(-4,12*order,tensor_hist(prev,P_hist)),(-2,6*order,tensor_hist(prev,D_hist))])
    if delta:
        prev=hist_H(r); order=3**r
        checks+=check_identity([(3,2*order,hist_H(r,1)),(-1,order,prev),(-2,4*order,tensor_hist(prev,V_hist))])
    H=hist_H(r,delta); size=3**r*2**delta
    assert sum(H.values())==size
    # Check Burnside average exactly by summing over all relevant S_n classes.
    weighted=Fraction(0)
    for t,cnt in H.items():
        typ=t+(1,)*(n-sum(t)); z=cent(typ)
        val=Fraction(z*cnt,size); assert val.denominator==1
        weighted+=val/z
        assert val/2==int(val/2)  # A_n classes unsplit, index halved
    assert weighted==1
    rows.append({'n':n,'r':r,'delta':delta,'subgroup_order':size,'S_n_detector_degree':factorial(n)//size,'A_n_detector_degree':factorial(n)//(2*size),'old_S_n_degree':factorial(n)//2,'multiplicity_bound':5**r*3**delta})

# Sharpness for the one-triple step: the 5-dimensional complement of the
# vertex module in the pair module for S5 has C3-invariant dimension 1.
from itertools import combinations
pairs=list(combinations(range(5),2))
def char5(p):
    return sum(tuple(sorted((p[i],p[j])))==(i,j) for i,j in pairs)-sum(p[i]==i for i in range(5))
assert char5(tuple(range(5)))==5
assert sum(char5(g) for g in C)==3
assert sum(char5(g) for g in A5)==0
S5=list(permutations(range(5)))
assert sum(char5(g) for g in S5)==0
assert sum(parity(g)*char5(g) for g in S5)==0

result={'status':'PASS','scope':'exact finite character arithmetic, not a numerical or formal proof of GRH','A5_identity':local,'A4_identity':local2,'S4_identity':small,'all_group_elements_checked_local':{'A5':60,'A4':12,'S4':24},'tower_class_coefficient_checks_n_5_to_60':checks,'one_triple_sharpness':{'dimension':5,'C3_fixed_dimension':1,'trivial_multiplicity':0,'sign_multiplicity_S5':0},'degree_table':rows}
with open('verification.json','w') as f:json.dump(result,f,indent=2);f.write('\n')
print('PASS:',checks,'tower class coefficients; all elements of A5, A4, S4; degree and mean checks for n=5..60')
