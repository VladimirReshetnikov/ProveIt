#!/usr/bin/env python3
"""Exact finite connected-Wick graph contraction for the second coefficient.
No numerical fitting, interpolation, or binary-matrix enumeration.
"""
from fractions import Fraction as F
from math import factorial
from itertools import product
from collections import defaultdict


def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def connected(r, edge_counts, pairs):
    reached={0}
    while True:
        nxt=reached|{v for (i,j),e in zip(pairs,edge_counts) if e and (i in reached or j in reached) for v in (i,j)}
        if nxt==reached: return len(reached)==r
        reached=nxt

def diagrams(degrees):
    r=len(degrees)
    pairs=[(i,j) for i in range(r) for j in range(i+1,r)]
    def rec(k,left,edges):
        if k==len(pairs):
            if any(x%2 for x in left): return
            if not connected(r,edges,pairs): return
            loops=[x//2 for x in left]
            den=1
            for e in edges: den*=factorial(e)
            for l in loops: den*=2**l*factorial(l)
            num=1
            for d in degrees: num*=factorial(d)
            mult=F(num,den)
            require(mult.denominator==1, "nonintegral Wick multiplicity")
            graph=[(i,j,e) for (i,j),e in zip(pairs,edges) if e]
            graph +=[(i,i,l) for i,l in enumerate(loops) if l]
            yield graph,int(mult)
            return
        i,j=pairs[k]
        for e in range(min(left[i],left[j])+1):
            new=list(left); new[i]-=e; new[j]-=e
            yield from rec(k+1,new,edges+[e])
    yield from rec(0,list(degrees),[])

def colorings(e):
    for a in range(e+1):
        for b in range(e-a+1):
            c=e-a-b
            yield a,b,c,F(factorial(e),factorial(a)*factorial(b)*factorial(c))*(-1)**c

def contract_graph(r, graph):
    out=defaultdict(F)
    for colors in product(*(list(colorings(e)) for i,j,e in graph)):
        parents=[list(range(r)),list(range(r))]
        powers=[[0]*r,[0]*r]
        def find(axis,i):
            while parents[axis][i]!=i: i=parents[axis][i]
            return i
        def merge(axis,i,j):
            parents[axis][find(axis,i)]=find(axis,j)
        coef=F(1)
        for (i,j,e),(a,b,c,weight) in zip(graph,colors):
            coef*=weight
            if a: merge(0,i,j)
            if b: merge(1,i,j)
            for v in (i,j):
                powers[0][v]+=b+c
                powers[1][v]+=a+c
        ps=[]
        for axis in (0,1):
            blocks=defaultdict(int)
            for i in range(r): blocks[find(axis,i)]+=powers[axis][i]
            ps+=list(blocks.values())
        if any(p%2 for p in ps): continue
        # Each component yields sum_i v_i^(2k)=s_k, including s_0=n.
        monomial=tuple(sorted(p//2 for p in ps))
        out[monomial]+=coef
    return {m:c for m,c in out.items() if c}

def cumulant_polynomial(degrees, q):
    out=defaultdict(F)
    count=0
    for graph,multiplicity in diagrams(degrees):
        count+=1
        for monomial,coef in contract_graph(len(degrees),graph).items():
            out[monomial]+=coef*multiplicity*q
    return {m:c for m,c in out.items() if c},count

def alpha(r): return F(3**r,2*r+1)

def asymptotic(poly, order):
    # s_r = n^(1-r) (3^r/(2r+1)+O(n^-2)). No first-order corrections.
    ans=F(0)
    for monomial,coef in poly.items():
        power=sum(1-r for r in monomial)
        require(power<=order, f"unexpected power: {monomial}, {power}, {order}")
        if power==order:
            for r in monomial: coef*=alpha(r)
            ans+=coef
    return ans

def eval_poly(poly,n):
    u=[F(2*i-n-1,2) for i in range(1,n+1)]
    S=sum(x*x for x in u)
    a=[x*x/S for x in u]
    maxr=max((max(m,default=0) for m in poly),default=0)
    sums=[sum(x**r for x in a) for r in range(maxr+1)]
    ans=F(0)
    for monomial,coef in poly.items():
        for r in monomial: coef*=sums[r]
        ans+=coef
    return ans

def encode(poly):
    return [{'coefficient':str(c),'s_indices':list(m)} for m,c in sorted(poly.items())]

def derive():
    targets={
        'cov_Q4_Q6':([4,6],F(1,12*45)),
        'cum3_Q4':([4,4,4],F(1,12**3)),
    }
    polys={}
    result={}
    for name,(degrees,q) in targets.items():
        poly,count=cumulant_polynomial(degrees,q)
        polys[name]=poly
        result[name]={'degrees':degrees,'connected_degree_graphs':count,'polynomial':encode(poly),'n2_limit':str(asymptotic(poly,-2)),'small_n_exact':{str(n):str(eval_poly(poly,n)) for n in range(2,7)}}
    m1=F(-9,5); m2=F(-39,100)
    v1=F(243,25); v2=F(-2691,175)
    f1=F(216,35); f2=F(-2484,175)
    g2=F(17,24)*(2*alpha(4)+8*alpha(3)+6*alpha(2)**2)
    d2=asymptotic(polys['cov_Q4_Q6'],-2)
    t2=asymptotic(polys['cum3_Q4'],-2)
    L1=-m1+v1/2-f1
    L2=-m2+v2/2-f2-g2+d2-t2/6
    c2=L2+L1**2/2
    vals=locals()
    result['constants']={key:str(vals[key]) for key in ['m1','m2','v1','v2','f1','f2','g2','d2','t2','L1','L2','c2']}
    require(L1==F(171,350), "first correction does not match")
    require(L2==F(6483,3500), 'second logarithmic coefficient mismatch')
    require(c2==F(483051,245000), 'second coefficient mismatch')
    result['constants']['phase_r2']=str(L2-1)
    require(L2-1==F(2983,3500), 'second phase coefficient mismatch')
    return result


# Human-readable exact formulas use x=s2, y=s3, z=s4 and s1=1.
# Keys below are powers (n,x,y,z); these are independently transcribed formulas.
COV46_FORMULA={
 (1,1,1,0):F(10,3),(0,2,0,0):F(34,3),(0,3,0,0):F(-52,3),
 (0,4,0,0):F(-2),(0,3,1,0):F(16,3),(0,2,1,0):F(148,3),
 (0,2,2,0):F(-5,3),(0,2,0,1):F(-40,3),(0,1,1,0):F(-40,3),
 (0,1,2,0):F(-76,3),(0,1,1,1):F(28,3),(0,1,0,1):F(-64,3),
 (0,0,1,0):F(4),(0,0,2,0):F(-22),(0,0,1,1):F(40),
 (0,0,0,1):F(16,3),(0,0,0,2):F(-10),
}
CUM444_FORMULA={
 (1,3,0,0):F(11),(0,2,0,0):F(37),(0,3,0,0):F(-104),
 (0,4,0,0):F(124),(0,5,0,0):F(40),(0,6,0,0):F(11,2),
 (0,4,1,0):F(-50),(0,3,1,0):F(-232),(0,3,0,1):F(70),
 (0,2,1,0):F(-114),(0,2,2,0):F(94),(0,2,0,1):F(50),
 (0,1,1,0):F(46),(0,1,2,0):F(258),(0,1,1,1):F(-210),
 (0,1,0,1):F(8),(0,0,1,0):F(2),(0,0,2,0):F(-22),
 (0,0,1,1):F(-102),(0,0,0,1):F(4),(0,0,0,2):F(90),
}

def simplify_polynomial(poly):
    out=defaultdict(F)
    for monomial,coef in poly.items():
        require(all(r<=4 for r in monomial), 'unexpected higher power sum')
        out[tuple(monomial.count(r) for r in (0,2,3,4))]+=coef
    return {m:c for m,c in out.items() if c}


