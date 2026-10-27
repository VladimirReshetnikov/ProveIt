#!/usr/bin/env python3
"""Exact certificate for the 10 -> 13 -> 7 cached contraction bound.

Standard library only.  A finite mathematical certificate, not a SAT solver.
The field-matrix algorithms and the inherited contraction interface are
mathematical dependencies; the checker does not implement those algorithms.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt
import json

R = 10
Q = 9
SCALE = 1_400_000
PLANS = [
 [[7,4,3,9],[1,6,0],[8,2,5]],
 [[5,4,6,7],[9,1,8],[2,3,0]],
 [[0,5,9,7],[2,1,4],[8,3,6]],
 [[0,4,7,8],[2,9,6],[1,5,3]],
 [[3,1,7,2],[9,6,8],[5,4,0]],
 [[7,1,5,8],[2,9,4],[0,6,3]],
 [[7,2,8,6],[5,9,3],[0,1,4]],
 [[1,9,6,7],[2,5,0],[4,3,8]],
 [[4,6,1,5],[8,9,2],[0,7,3]],
]
# epsilon = 1/100000.  First branch weights (1+eps/2,1+eps/2,0).
# Second branch weights (1,47/56+eps,15/28).
WEIGHTS = sorted(set(permutations((1_400_007,1_400_007,0))) |
                 set(permutations((1_400_000,1_175_014,750_000))))
MIXING_WEIGHTS = [137,124,135,120,108,119,106,87,64]
MIXING_DENOMINATOR = 1000
EXPECTED_B2 = F(15_952_347_164_548_384_057, 49_000_000_000_000_000_000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def operation_parts(r, blocks):
    require(len(blocks)==3 and all(blocks), 'three nonempty blocks required')
    require(sorted(x for b in blocks for x in b) == list(range(r)), 'bad plan')
    parts = []
    universe = set(range(r))
    def build(block):
        if len(block) == 1:
            return
        k = len(block)//2
        left,right = block[:k],block[k:]
        build(left)
        build(right)
        parts.append((left,right,sorted(universe-set(block))))
    for block in blocks:
        build(block)
    parts.append(blocks)
    require(len(parts) == r-2, 'wrong operation count')
    return parts


def supports(r, blocks):
    edges = list(combinations(range(r),2))
    out = []
    for parts in operation_parts(r,blocks):
        labels = {v:j for j,part in enumerate(parts) for v in part}
        for weights in WEIGHTS:
            coeffs = dict(zip(((0,1),(0,2),(1,2)),weights))
            out.append(tuple(0 if labels[x] == labels[y] else
                             coeffs[tuple(sorted((labels[x],labels[y])))]
                             for x,y in edges))
    return out


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def certificate():
    menus = [supports(R,p) for p in PLANS]
    require(all(len(v)==72 for v in menus), 'wrong support count')
    require(len(MIXING_WEIGHTS)==Q and min(MIXING_WEIGHTS)>=0,
            'bad mixing weights')
    require(sum(MIXING_WEIGHTS)==MIXING_DENOMINATOR,'bad weight denominator')
    norms = [[dot(v,v) for v in menu] for menu in menus]
    pair_maxima = [[0]*Q for _ in range(Q)]
    witnesses = {}
    for i,j in combinations(range(Q),2):
        wi,wj=MIXING_WEIGHTS[i],MIXING_WEIGHTS[j]
        value,ki,kj = max((wi*wi*norms[i][ki]+wj*wj*norms[j][kj]+
                           2*(Q-1)*wi*wj*dot(v,w),ki,kj)
                          for ki,v in enumerate(menus[i])
                          for kj,w in enumerate(menus[j]))
        pair_maxima[i][j] = pair_maxima[j][i] = value
        witnesses[f'{i},{j}'] = [ki,kj]
    pair_sum=sum(pair_maxima[i][j] for i,j in combinations(range(Q),2))
    U=F(pair_sum,(Q-1)*MIXING_DENOMINATOR*MIXING_DENOMINATOR)
    b2 = 2*U/F(SCALE*SCALE*R*R)
    require(b2 == EXPECTED_B2,'wrong coefficient')
    return {'status':'PASS','groups':R,'plans':Q,'supports_per_plan':72,
            'mixing_weights':MIXING_WEIGHTS,'weight_denominator':MIXING_DENOMINATOR,
            'pairwise_support_choices_checked':36*72*72,'U':str(U),
            'b_squared':str(b2),'pair_maxima':pair_maxima,
            'maximizer_indices':witnesses}


def select_plan(directed_dimensions):
    """Positive integer dimensions. No logarithms or floating-point choices."""
    dimensions=[]
    for x,y in combinations(range(R),2):
        a,b=directed_dimensions[x,y],directed_dimensions[y,x]
        require(type(a) is int and type(b) is int and a>0 and b>0,'invalid size')
        dimensions.append(a*b)
    scores=[]
    for plan in PLANS:
        best=0
        for support in supports(R,plan):
            value=1
            for d,v in zip(dimensions,support):
                value *= pow(d,v)
            best=max(best,value)
        scores.append(best)
    j=min(range(Q),key=lambda j:(scores[j],j))
    return j,scores[j]


def atan_bounds(inv,n=100):
    x=F(1,inv)
    value=sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    following=value+((-1)**n*x**(2*n+1)/F(2*n+1))
    return min(value,following),max(value,following)


def transcendental_bounds():
    a,b=atan_bounds(5);c,d=atan_bounds(239)
    pi=(16*a-4*d,16*b-4*c)
    n=110
    lnlo=2*sum((F(1,3)**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    # Tail <= 2 * 3^(-2n-1) / ((2n+1)*(1-1/9)).
    tail=2*F(1,3)**(2*n+1)/F(2*n+1)/F(8,9)
    return pi,(lnlo,lnlo+tail)


def sqrt_bounds(x,places=40):
    d=10**places
    n=isqrt(x.numerator*d*d//x.denominator)
    return F(n,d),F(n+1,d)


def coefficient_bounds(radicals):
    pi,ln=transcendental_bounds()
    rr=[sqrt_bounds(x) for x in radicals]
    return pi[0]/ln[1]*sum((x[0] for x in rr),F(0)),pi[1]/ln[0]*sum((x[1] for x in rr),F(0))


def schedule():
    eta0,eta1,eta2,rho=F(301,20000),F(119,10000),F(1549,324000),F(4,9)
    require(eta0+eta1+eta2/(1-rho)==F(8,225),'capacity mismatch')
    require(10**1000 < 2**3322,'log2(10) upper bound failed')
    require(13**1000 < 2**3701,'log2(13) upper bound failed')
    require(7**100 < 2**281,'log2(7) upper bound failed')
    gaps=[1-F(9,10)-2*eta0*F(3322,1000),
          1-F(9,10)-(eta0+eta1)*F(3701,1000),
          1-F(9,10)-F(8,225)*F(281,100)]
    require(all(g>0 for g in gaps),'nonpositive packing gap')
    require(F(8,225)*(1+2*F(3701,1000))<1,'fresh-side packing bound failed')
    require(F(3,4)>F(632,1225),'tail local cost not dominated')
    rad0=[2*EXPECTED_B2/eta0]
    rad1=[F(7200,301),F(50304,20111)]
    radinf=[F(7200,301),F(19200,20111),F(77760,261781)]
    C0,C1,Cinf=(coefficient_bounds(x) for x in (rad0,rad1,radinf))
    require(C0[1]<F(29812,1000),'root exceeds eventual29.812')
    require(C1[1]<C0[0] and Cinf[1]<C0[0],'root is not the maximum')
    return {'status':'PASS','etas':list(map(str,(eta0,eta1,eta2))),
            'tail_ratio':str(rho),'packing_gaps':list(map(str,gaps)),
            'coefficient_intervals':[[str(a),str(b)] for a,b in (C0,C1,Cinf)],
            'decimal_for_display_only':[float(C[0]) for C in (C0,C1,Cinf)],
            'eventual_time_and_space_coefficient':'29.812'}



def check_rectangle_supports():
    count=0
    for x in range(11):
        for y in range(11):
            for z in range(11):
                hi,mid,lo=sorted((x,y,z),reverse=True)
                direct=max(1_400_007*(hi+mid),
                           1_400_000*hi+1_175_014*mid+750_000*lo)
                supported=max(a*x+b*y+c*z for a,b,c in WEIGHTS)
                require(direct==supported,'rectangular support mismatch')
                count+=1
    return {'sorted_dimension_triples_checked':count,'status':'PASS'}


def legacy_supports(r, blocks):
    edges=list(combinations(range(r),2));rows=[]
    for parts in operation_parts(r,blocks):
        labels={v:j for j,p in enumerate(parts) for v in p}
        for discounted in ((0,1),(0,2),(1,2)):
            rows.append(tuple(0 if labels[a]==labels[b] else
                              2 if tuple(sorted((labels[a],labels[b])))==discounted
                              else 5 for a,b in edges))
    return rows


def check_legacy_tail_plans():
    from itertools import product
    plans13=[[[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],
             [[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],
             [[0,8,11,12,1],[7,10,4,3],[5,2,6,9]]]
    menus=[legacy_supports(13,p) for p in plans13]
    maximum=0
    for a,b,c in product(*menus):
        maximum=max(maximum,sum((x+y+z)**2 for x,y,z in zip(a,b,c)))
    require(maximum==7074,'legacy13 certificate changed')
    b13=F(2*maximum,25*9*13*13)
    require(b13==F(1572,4225),'legacy13 normalization')
    masks7=legacy_supports(7,[[0,1,2],[3,4],[5,6]])
    b7=F(2*max(dot(v,v) for v in masks7),25*49)
    require(b7==F(632,1225),'legacy7 normalization')
    return {'status':'PASS','r13_support_tuples':33**3,'r13_Q':maximum,
            'r13_b_squared':str(b13),'r7_b_squared':str(b7)}

if __name__=='__main__':
    print(json.dumps({'certificate':certificate(),'schedule':schedule(),
                      'rectangle_supports':check_rectangle_supports(),
                      'legacy_tail':check_legacy_tail_plans()},indent=2))
