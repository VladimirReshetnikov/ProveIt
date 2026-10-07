#!/usr/bin/env python3
"""Exact finite checks for fixed-radius Bohr invariance.

Standard library only. These checks supplement the article's proofs; they
are not proof-assistant certificates. No assert statements are used, so
running with python -O does not disable validation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, gcd, prod
from pathlib import Path
import json
import random


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def tnorm(x: F) -> F:
    x %= 1
    return min(x, 1-x)


class Group:
    def __init__(self, moduli: tuple[int, ...]):
        require(bool(moduli) and all(n > 0 for n in moduli), 'invalid group')
        self.moduli = moduli
        self.points = list(product(*(range(n) for n in moduli)))

    def add(self, x: tuple[int, ...], y: tuple[int, ...], k: int = 1):
        return tuple((a+k*b) % n for a,b,n in zip(x,y,self.moduli))

    def distances(self, chars: tuple[tuple[int, ...], ...]):
        return {x: tuple(tnorm(sum((F(a*b,n) for a,b,n in
                                   zip(c,x,self.moduli)), F(0)))
                         for c in chars) for x in self.points}


def bohr(dist, widths):
    return {x for x, ds in dist.items() if all(a <= b for a,b in zip(ds,widths))}


def check_instance(g, dist, widths, m, d, B=None, large=None):
    require(m >= 1 and all(0 < a <= F(1,4) for a in widths), 'bad input')
    require(all(v <= a/(2*m) for v,a in zip(dist[d], widths)), 'step too large')
    if B is None:
        B = bohr(dist, widths)
    if large is None:
        large = bohr(dist, tuple(F(3,2)*a for a in widths))
    expanded = bohr(dist, tuple(a+m*v for a,v in zip(widths, dist[d])))
    plus = {x for x in B if g.add(x,d) not in B}
    minus = {x for x in B if g.add(x,d,-1) not in B}
    require(len(plus) == len(minus), 'exit cardinalities differ')
    require(len(large) <= 3**len(widths)*len(B), 'box packing fails')
    used = set()
    for sign, exits in ((1,plus),(-1,minus)):
        for x in exits:
            require(all(g.add(x,d,sign*j) not in B for j in range(1,2*m+1)),
                    'early reentry')
        for j in range(1,m+1):
            tube = {g.add(x,d,sign*j) for x in exits}
            require(len(tube) == len(exits), 'translation is not injective')
            require(not tube & used, 'tube collision')
            require(tube <= expanded-B, 'tube outside claimed shell')
            used |= tube
    require(2*m*len(plus) <= len(expanded)-len(B), 'intrinsic inequality fails')
    require(expanded <= large, 'expansion containment fails')
    return len(plus) > 0


def cyclic_checks():
    counts = dict(bohr_sets=0, admissible_steps=0, positive_exit_steps=0)
    radii = (F(1,4),F(1,5),F(1,6),F(1,8),F(2,9),F(1,12))
    for n in range(2,33):
        g = Group((n,))
        for r in range(0, (3 if n <= 17 else 2)+1):
            for K in combinations(range(n//2+1),r):
                dist = g.distances(tuple((k,) for k in K))
                for rho in radii:
                    widths = (rho,)*r
                    B = bohr(dist, widths)
                    large = bohr(dist, (F(3,2)*rho,)*r)
                    require(len(large) <= 3**r*len(B), 'packing failure')
                    counts['bohr_sets'] += 1
                    for m in (1,2,3,4,8):
                        for d in bohr(dist, (rho/(2*m),)*r):
                            counts['admissible_steps'] += 1
                            counts['positive_exit_steps'] += int(check_instance(
                                g, dist, widths, m, d, B, large))
    return counts


def product_checks():
    rng = random.Random(20261006)
    moduli_list = ((4,6),(5,5),(3,7),(2,3,5),(7,11),(4,4,4),(9,))
    radii = (F(1,4),F(1,5),F(1,6),F(1,8),F(2,9))
    counts = dict(bohr_sets=0, admissible_steps=0, positive_exit_steps=0)
    for _ in range(500):
        g = Group(rng.choice(moduli_list))
        r = rng.randrange(1,5)
        chars = tuple(rng.choice(g.points) for _ in range(r))
        dist = g.distances(chars)
        widths = tuple(rng.choice(radii) for _ in range(r))
        B = bohr(dist,widths)
        large = bohr(dist,tuple(F(3,2)*a for a in widths))
        counts['bohr_sets'] += 1
        for m in (1,2,3):
            for d in bohr(dist,tuple(a/(2*m) for a in widths)):
                counts['admissible_steps'] += 1
                counts['positive_exit_steps'] += int(check_instance(
                    g,dist,widths,m,d,B,large))
    return counts


def sharpness_checks():
    g = Group((101,))
    dist = g.distances(((1,),))
    B,large = bohr(dist,(F(20,101),)), bohr(dist,(F(30,101),))
    d,m = (1,),10
    require(check_instance(g,dist,(F(20,101),),m,d), 'no exits')
    b = len(B-{g.add(x,d) for x in B})
    require(2*m*b == len(large)-len(B) == 20, 'rank-one equality fails')
    packing = []
    for r in range(1,5):
        g = Group((5,)*r)
        chars = tuple(tuple(int(i==j) for i in range(r)) for j in range(r))
        dist = g.distances(chars)
        B = bohr(dist,(F(3,20),)*r)
        large = bohr(dist,(F(9,40),)*r)
        require(len(B)==1 and len(large)==3**r, 'packing equality fails')
        packing.append({'rank':r,'small':len(B),'large':len(large)})
    return {'tube_equality':{'N':101,'rho':'20/101','m':10,'defect':b,
                            'small':41,'large':61}, 'packing_equalities':packing}


def product_spikes():
    records=[]
    p,L=5,7
    q=L*p-1
    for s in range(1,4):
        g=Group((q,)+(p,)*s)
        chars=[(1,)+(0,)*s]
        for i in range(s):
            for sign in (1,-1):
                chars.append((sign%q,)+tuple(int(j==i) for j in range(s)))
        dist=g.distances(tuple(chars))
        B=bohr(dist,(F(1,p),)*(2*s+1))
        I={x%q for x in range(-(L-1),L)}
        expected={(x,)+(0,)*s for x in I}
        expected|={(0,)+y for y in product((0,1,p-1),repeat=s)}
        require(B==expected,'product spike description fails')
        d=(1,)+(0,)*s
        b=len(B-{g.add(x,d) for x in B})
        require(b==3**s,'product spike defect fails')
        require(len(B)==2*L-2+3**s,'product spike size fails')
        check_instance(g,dist,(F(1,p),)*(2*s+1),1,d,B)
        records.append({'s':s,'moduli':list(g.moduli),'size':len(B),
                        'defect':b,'relative_step':str(F(p,q)),
                        'normalized_ratio':str(F(b*q,p*len(B)))})
    return records


def crt_parameters(s,L):
    D=factorial(s)
    R=[L*i*D+1 for i in range(1,s+1)]
    P=prod(R)**2
    Pi=[P+i*D for i in range(1,s+1)]
    q=L*P-1
    require(P>L*s*D and P>=100,'parameter size')
    require(P%D==1%D,'factorial residue')
    require(all(gcd(a,b)==1 for a,b in combinations([q]+Pi,2)), 'not CRT coprime')
    require(all(F(i*D,P*Pi[i-1])<F(1,q) for i in range(1,s+1)), 'slack')
    N=q*prod(Pi)
    d=(prod(Pi)*pow(prod(Pi),-1,q))%N
    K=[N//q]
    for v in Pi:
        K += [(N//v+N//q)%N,(N//v-N//q)%N]
    require(len(set(K))==2*s+1,'characters not distinct')
    require(d%q==1 and all(d%v==0 for v in Pi),'CRT step')
    require(all(tnorm(F(k*d,N))==F(1,q) for k in K),'character step')
    return P,Pi,q,N,d,K


def crt_checks():
    records=[]
    for s in range(1,7):
        L=3**(2*s)
        P,Pi,q,N,d,K=crt_parameters(s,L)
        size,defect=2*L-2+3**s,3**s
        ratio=F(defect*q,P*size)
        require(ratio>F(3**s,3),'weak exponential bound fails')
        require(ratio<F(3**s,2),'limit upper check fails')
        records.append({'s':s,'rank':2*s+1,'L':L,'P':str(P),'Pi':[str(v) for v in Pi],
                        'q':str(q),'N':str(N),'step':str(d),'frequencies':[str(k) for k in K],
                        'size':size,'defect':defect,'relative_step':str(F(P,q)),
                        'normalized_ratio':str(ratio)})
    # Brute-force the first genuinely cyclic certificate, N=90799.
    P,Pi,q,N,d,K=crt_parameters(1,9)
    B={x for x in range(N) if all(min((k*x)%N,(-k*x)%N)*P<=N for k in K)}
    b=len(B-{(x+d)%N for x in B})
    require(len(B)==19 and b==3,'CRT brute force fails')
    return {'parameter_certificates':records,
            'brute_force':{'N':N,'rank':3,'size':len(B),'defect':b}}


def four_vertex_checks():
    cases=0
    # Test the raw tree-intersection bound, before any positivity assumption.
    for n in range(1,8):
        for mask in range(1,1<<n):
            B={x for x in range(n) if (mask>>x)&1}
            As=[B]+[B-{x} for x in sorted(B)]
            for a,b,c in product(range(n),repeat=3):
                v=(0,a,(a+b)%n,c)
                edges=(a,b,c)
                loss=sum(len(B-{(x+d)%n for x in B}) for d in edges)
                for A in As:
                    common=set.intersection(*({(x+t)%n for x in A} for t in v))
                    bound=len(B)-loss-4*len(B-A)
                    require(len(common)>=bound,'four-vertex bound')
                    cases+=1
    return {'intersection_cases':cases}


def comparison_checks():
    rows=[]
    for r in (1,2,3,5,10,20):
        rho=F(1,100)
        old=rho**r/(2**(r+4)*r)
        new=rho/(8*(3**r-1))
        require(new>old,'radius improvement fails')
        require(new/old==F(2**(r+1)*r,3**r-1)*rho**(1-r),'ratio identity')
        rows.append({'rank':r,'rho':str(rho),'old_radius':str(old),
                     'new_radius':str(new),'gain':str(new/old)})
    return rows


def scalar_and_freiman_checks():
    cases=0
    for r in range(1,31):
        c=3**r-1
        require(c<=2*4**(r-1), 'gain induction bound')
        require(1-3*F(c,6*c+2)-F(1,2)==F(1,6*c+2), 'extension-only residual')
        require(1-3*F(c,8*c)-F(1,2)==F(1,8), 'margin residual')
        for denom in range(4,31):
            rho=F(1,denom)
            gain=F(2**(r+1)*r,c)*rho**(1-r)
            require(gain>=2**r*r, 'radius gain lower bound')
            cases+=1
        for k in range(2,13):
            eta=F(1,4*k)
            threshold=F((2*k-1)*c,2)/(1-2*k*eta)
            m=threshold.numerator//threshold.denominator+1
            require((2*k-1)*F(c,2*m)+2*k*eta<1, 'higher order budget')
            cases+=1
    require(2*(1-F(5,14))*F(7,8)==F(9,8), '5/14 threshold')
    require(F(5,14)**2<F(1,2), 'common-fibre budget')
    # A nonconstant partial map into the torsion-free group Z.
    n=211
    B={x%n for x in range(-40,41)}
    holes={x%n for x in (-37,-29,-17,-3,6,11,23,34)}
    A=B-holes
    lift=lambda x: x if x<=n//2 else x-n
    psi={x:2*lift(x)+7 for x in A}
    pairs={}
    for x,y in product(A,repeat=2):
        key=(x+y)%n
        value=psi[x]+psi[y]
        if key in pairs:
            require(pairs[key]==value, 'test input is not Freiman-2')
        pairs[key]=value
    C={x%n for x in range(-4,5)}
    induced={}
    for x,y in product(A,repeat=2):
        key=(x-y)%n
        if key in C:
            value=psi[x]-psi[y]
            if key in induced:
                require(induced[key]==value,'induced difference is ambiguous')
            induced[key]=value
    require(set(induced)==C,'difference coverage')
    for k in (2,3):
        kappa=max(F(len(B-{(x+d)%n for x in B}),len(B)) for d in C)
        eta=F(len(holes),len(B))
        require((2*k-1)*kappa+2*k*eta<1,'test extension budget')
        sums={}
        for tup in product(C,repeat=k):
            key=sum(tup)%n
            value=sum(induced[d] for d in tup)
            if key in sums:
                require(sums[key]==value,'induced map is not Freiman-k')
            sums[key]=value
    return {'scalar_cases':cases, 'local_map_example':
            {'N':n,'B_size':len(B),'A_size':len(A),'C_size':len(C),
             'target':'integers','verified_orders':[2,3]},
            'compatibility_threshold':'5/14 (exact boundary identity)'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results'/'verification.json')
    args=parser.parse_args()
    data={'arithmetic':'exact integers and fractions; no floating-point tests',
          'seed':20261006,'cyclic':cyclic_checks(),'anisotropic_products':product_checks(),
          'sharpness':sharpness_checks(),'product_spikes':product_spikes(),
          'cyclic_spikes':crt_checks(),'four_vertex':four_vertex_checks(),
          'radius_comparison':comparison_checks(),
          'scalar_and_freiman':scalar_and_freiman_checks()}
    data['status']='all checks passed'
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps({k:data[k] for k in ('status','cyclic','anisotropic_products','four_vertex')},indent=2))

if __name__=='__main__':
    main()
