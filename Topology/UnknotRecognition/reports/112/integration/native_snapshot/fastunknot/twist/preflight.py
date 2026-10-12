"""Exact chain-size certification without constructing the chain complex.

Evaluate the Temperley--Lieb product prod(I + |e_j| E_{i_j}) at loop value 2,
then take half the ordinary closure trace. This is a dimension computation,
not a knot invariant and not a recognition test.
"""
from __future__ import annotations
from collections import defaultdict
from .core import Run, ResourceLimit, validate_runs


def _compose_e(matching: tuple[int, ...], i: int):
    b=len(matching)//2
    parent=list(range(3*b))
    def find(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]]; v=parent[v]
        return v
    def join(x,y):
        x,y=find(x),find(y)
        if x!=y: parent[y]=x
    for x,y in enumerate(matching):
        if x<y: join(x,y)
    join(b+i,b+i+1); join(2*b+i,2*b+i+1)
    for j in range(b):
        if j not in (i,i+1): join(b+j,2*b+j)
    outside=defaultdict(list)
    for new,old in enumerate(list(range(b))+list(range(2*b,3*b))):
        outside[find(old)].append(new)
    loops=len({find(x) for x in range(3*b)}-outside.keys())
    out=[0]*(2*b)
    for pair in outside.values():
        if len(pair)!=2: raise ArithmeticError('invalid Temperley--Lieb matching')
        x,y=pair; out[x]=y; out[y]=x
    return tuple(out),loops


def _closure_circles(matching):
    b=len(matching)//2
    visited=set(); count=0
    for v in range(2*b):
        if v in visited: continue
        count+=1; stack=[v]; visited.add(v)
        while stack:
            x=stack.pop()
            for y in (matching[x],(x+b)%(2*b)):
                if y not in visited: visited.add(y); stack.append(y)
    return count


def basis_size(strands: int, runs, *, max_matchings: int=4096, max_strands: int=256, check=None) -> dict:
    check = (lambda: None) if check is None else check
    check()
    runs=validate_runs(strands,runs)
    if type(max_matchings) is not int or max_matchings<1:
        raise ValueError('max_matchings must be a positive integer')
    if type(max_strands) is not int or max_strands<1:
        raise ValueError('max_strands must be a positive integer')
    if strands>max_strands: raise ResourceLimit('preflight strand limit exceeded')
    identity=tuple((x+strands)%(2*strands) for x in range(2*strands))
    states={identity:1}; plans={}; peak=1; transitions=0
    for r in runs:
        check()
        new=dict(states)
        for matching,coefficient in states.items():
            check()
            key=(matching,r.generator-1)
            if key not in plans: plans[key]=_compose_e(*key)
            out,loops=plans[key]
            new[out]=new.get(out,0)+abs(r.exponent)*coefficient*(1<<loops)
            transitions+=1
            if len(new)>max_matchings: raise ResourceLimit('preflight matching limit exceeded')
        states=new; peak=max(peak,len(states))
    check()
    total=sum(coefficient*(1<<(_closure_circles(matching)-1)) for matching,coefficient in states.items())
    return {'exact_basis':total,'peak_matchings':peak,'transitions':transitions,
            'compiled_plans':len(plans),'basis_bit_length':total.bit_length(),
            'method':'Temperley-Lieb dimension trace at loop value 2'}


def generator_basis_bound(strands: int, runs, *, max_strands: int = 10000) -> int:
    """Sharp first-use product bound prod_i (3+prod_{j:i_j=i}(1+2m_j))/2.

    Each first use of an Artin generator must merge circles; later uses can
    increase their number by at most one. See the proof in the article.
    """
    runs=validate_runs(strands,runs)
    if strands>max_strands: raise ResourceLimit('bound strand limit exceeded')
    products={}
    for r in runs:
        products[r.generator]=products.get(r.generator,1)*(1+2*abs(r.exponent))
    value=1 << (strands-1-len(products))
    for p in products.values(): value *= (3+p)//2
    return value


def degree_profile(strands: int, runs, *, max_matchings: int=4096,
                   max_crossings: int=10000, max_strands: int=256,
                   max_coefficient_steps: int=20000000) -> dict:
    """Exact homological chain dimensions by a TL polynomial transfer.

    Each E coefficient is a consecutive geometric sum, so convolution uses
    a sliding window. This does NOT compute homology or any differential.
    The bound is polynomial in the expanded crossing count for fixed strands.
    """
    runs=validate_runs(strands,runs)
    for name,value in [('max_matchings',max_matchings),('max_crossings',max_crossings),
                       ('max_strands',max_strands),('max_coefficient_steps',max_coefficient_steps)]:
        if type(value) is not int or value<0: raise ValueError(name+' must be nonnegative')
    if max_matchings<1 or strands>max_strands: raise ResourceLimit('profile geometry limit exceeded')
    n=sum(abs(r.exponent) for r in runs)
    if n>max_crossings: raise ResourceLimit('profile expanded-crossing limit exceeded')
    identity=tuple((x+strands)%(2*strands) for x in range(2*strands))
    states={identity:[1]}; plans={}; length=1; low_degree=0; steps=0; peak=1
    for r in runs:
        m=abs(r.exponent); newlen=length+m; new={}
        ioffset=0 if r.exponent>0 else m
        lo,hi=(1,m) if r.exponent>0 else (0,m-1)
        for matching,poly in states.items():
            steps+=length+newlen
            if steps>max_coefficient_steps: raise ResourceLimit('profile coefficient-step limit exceeded')
            dst=new.setdefault(matching,[0]*newlen)
            for k,a in enumerate(poly): dst[k+ioffset]+=a
            key=(matching,r.generator-1)
            if key not in plans: plans[key]=_compose_e(*key)
            target,loops=plans[key]
            out=new.setdefault(target,[0]*newlen)
            window=0
            for k in range(newlen):
                a=k-lo; z=k-hi-1
                if 0<=a<length: window+=poly[a]
                if 0<=z<length: window-=poly[z]
                out[k]+=window<<loops
            if len(new)>max_matchings: raise ResourceLimit('profile matching limit exceeded')
        states=new;length=newlen;peak=max(peak,len(states))
        if r.exponent<0: low_degree-=m
    totals=[0]*length
    for matching,poly in states.items():
        shift=_closure_circles(matching)-1
        for k,a in enumerate(poly): totals[k]+=a<<shift
    dims={low_degree+k:a for k,a in enumerate(totals) if a}
    return {'chain_dimensions':dims,'exact_basis':sum(totals),
            'matrix_bit_upper_bound':sum(a*dims.get(h+1,0) for h,a in dims.items()),
            'rank_xor_bit_upper_bound':sum(a*dims.get(h+1,0)*min(a,dims.get(h+1,0)) for h,a in dims.items()),
            'peak_chain_dimension':max(totals),'peak_matchings':peak,
            'coefficient_steps':steps,'method':'TL dimension-profile transfer with sliding windows'}
