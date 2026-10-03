#!/usr/bin/env python3
"""Finite audits; the unrestricted conservation proof is in PROOF.md."""
from itertools import product
from random import Random
from math import isqrt
import json
W={'u':1,'E':2,'W':2}

def require(condition, message='audit condition failed'):
    if not condition:
        raise RuntimeError(message)

def add(p,q): return tuple(x+y for x,y in zip(p,q))
def norm(p): return max(map(abs,p))
def near(p,q,r): return max(abs(x-y) for x,y in zip(p,q)) <= r

def action(c,a,planar=True):
    """Exact radius-4 input predicate and radius-2 write rule at head a."""
    if c.get(a) not in ('E','W'): return {}
    if any(b!=a and s in ('E','W') and near(a,b,4) for b,s in c.items()): return {}
    def p(x,y=0): return add(a,(x,y))
    s=c[a]
    if s=='E':
        if p(1) not in c: return {a:None,p(1):'E'}
        if c.get(p(1))=='u' and p(2,1 if planar else 0) not in c:
            return {a:'W',p(1):None,p(2,1 if planar else 0):'u'}
    else:
        if p(-1) not in c: return {a:None,p(-1):'W'}
        if c.get(p(-1))=='u':
            if not planar: return {a:'E'}
            if p(0,1) not in c and p(-1,1) not in c:
                return {a:None,p(-1):None,p(0,1):'E',p(-1,1):'u'}
    return {}

def step(c,planar=True):
    out=dict(c); used=set()
    for a,s in c.items():
        if s not in ('E','W'): continue
        ac=action(c,a,planar)
        require(not (used & ac.keys()), 'writes overlap')
        used.update(ac)
        for b,z in ac.items():
            if z is None: out.pop(b,None)
            else: out[b]=z
    return out

def local_value(c,x,planar=True):
    """Cellwise radius-6 evaluation strategy; reuses action() predicates."""
    neighborhood={y:s for y,s in c.items() if near(x,y,6)}
    writes=[]
    for a,s in neighborhood.items():
        if s in ('E','W') and near(x,a,2):
            ac=action(neighborhood,a,planar)
            if x in ac: writes.append(ac[x])
    require(len(writes)<=1, 'multiple cellwise writers')
    return writes[0] if writes else c.get(x)

def mass(c):return sum(W[z] for z in c.values())
def initial(k):return {(0,0):'u',(k,0):'u',(1,0):'E'}
def T(n,k):return n*n+(2*k-3)*n

def checks():
    # This deliberate failure must still raise under python -O.
    try:
        require(False, 'guard self-test')
    except RuntimeError as error:
        require(str(error)=='guard self-test', 'unexpected guard self-test error')
    else:
        raise RuntimeError('require() did not enforce its condition')
    rng=Random(813219); trials=2500; cells_checked=0
    for trial in range(trials):
        c={}
        # Sparse and crowded configurations, with extra unit noise and inactive heads.
        for _ in range(rng.randrange(0,32)):
            c[(rng.randrange(-12,13),rng.randrange(-12,13))]=rng.choice(('u','u','E','W'))
        if trial%3==0:
            for a in ((0,0),(5,0),(-5,0)):
                c[a]=rng.choice(('E','W'))
        for planar in (False,True):
            nxt=step(c,planar)
            require(mass(nxt)==mass(c), 'malformed configuration mass changed')
            if trial<100:
                sites=set(c)|set(nxt)
                for a in c:
                    sites.update(add(a,z) for z in product(range(-2,3),repeat=2))
                for x in sites:
                    require(local_value(c,x,planar)==nxt.get(x), 'cellwise and global evaluations differ')
                    cells_checked+=1
    stationary_boxes=[]
    for k in (3,5,8):
        for planar in (False,True):
            c=initial(k); visited=set(c); next_n=1
            for t in range(1,T(151,k)+1):
                c=step(c,planar); visited.update(c)
                require(mass(c)==4, 'shuttle mass changed')
                if t==T(next_n,k):
                    n=next_n; row=n if planar else 0
                    require(c=={(0,row):'u',(k+n,row):'u',(1,row):'E'}, 'section configuration differs')
                    if planar:
                        require(len(visited)==n*(n-1)//2+(k+1)*n+3, 'planar prefix site count differs')
                    else: require(visited=={(x,0) for x in range(k+n+1)}, 'rank-one prefix site set differs')
                    next_n+=1
            if planar:
                for N in range(k,150):
                    actual=sum(max(abs(x),abs(y))<=N for x,y in visited)
                    expected=(N*N+(2*k+3)*N+2+k-k*k)//2
                    require(actual==expected, 'stationary box count differs')
                stationary_boxes.append({'k':k,'checked_N':[k,149]})
    # Same-plane vertical drift. Shift after each G step, equivalently add t to y.
    drift_checks=[]
    for k in (3,5,8):
        c=initial(k); visited=set(c); byrow={}
        for x,y in c:byrow.setdefault(y,set()).add(x)
        for t in range(1,12001):
            c=step(c,True)
            for x,y in c:
                z=(x,y+t); visited.add(z);byrow.setdefault(y+t,set()).add(x)
        Ns=(max(2*k+4,30),100,999,5000,10000)
        for N in Ns:
            actual=sum(max(abs(x),abs(y))<=N for x,y in visited)
            # L/H holes y_n-1=n²+(2k-2)n-1, n>=1.
            lholes=max(0,isqrt((k-1)**2+N+1)-(k-1))
            # R holes z_n=n²+(2k-1)n+k-1, n>=0.
            root=(isqrt((2*k-1)**2+4*(N-k+1))-(2*k-1))//2
            rholes=max(0,root+1)
            expected=3*(N+1)-2*lholes-rholes
            require(actual==expected, ('drift count differs',k,N,actual,expected,lholes,rholes))
            drift_checks.append({'k':k,'N':N,'count':actual,'L_H_holes':lholes,'R_holes':rholes})
    return {'receipt_type':'sparse_orbit_geometry_audit','schema_version':1,'status':'passed','check_method':'explicit RuntimeError guards','guard_self_test':'passed','malformed_configuration_trials':trials,'both_rule_variants':True,'cellwise_values_checked':cells_checked,'sections_checked_per_k_variant':151,'stationary_box_checks':stationary_boxes,'same_plane_drift_box_checks':drift_checks,'warning':'Finite tests audit implementation and formulas; they do not replace proofs.'}
if __name__=='__main__': print(json.dumps(checks(),indent=2))
