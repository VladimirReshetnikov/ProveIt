"""Optimal formal conjugation degree for FIXED Wirtinger seed arcs.

A crossing (o,u,v,eps) asserts v=o^eps*u*o^-eps. This module validates
combinatorial indices, not planar realizability or the number of link components.
It retains all original crossing relations in the exported presentation.
"""
from __future__ import annotations
from heapq import heappop, heappush
from .slp import Arena


def validate(n, crossings, seeds):
    if type(n) is not int or n < 1:
        raise ValueError('positive arc count required')
    if not seeds or any(type(v) is not int or not 0 <= v < n for v in seeds):
        raise ValueError('nonempty valid seed set required')
    for crossing in crossings:
        if len(crossing) != 4:
            raise ValueError('crossings are (over, under_in, under_out, sign)')
        o,u,v,e = crossing
        if any(type(x) is not int or not 0 <= x < n for x in (o,u,v)) or e not in (-1,1):
            raise ValueError('invalid crossing')


def minimum_degrees(n: int, crossings, seeds):
    crossings = tuple(tuple(x) for x in crossings)
    seeds = frozenset(seeds)
    validate(n,crossings,seeds)
    hyperarcs = []
    incidence = [[] for _ in range(n)]
    for i,(o,u,v,e) in enumerate(crossings):
        for source,target,orientation in ((u,v,1),(v,u,-1)):
            index = len(hyperarcs)
            hyperarcs.append((o,source,target,i,orientation))
            for x in {o,source}: incidence[x].append(index)
    remaining = [len({o,u}) for o,u,_,_,_ in hyperarcs]
    distance = [None]*n
    settled = [False]*n
    parent = [None]*n
    heap = []
    for v in seeds:
        distance[v]=1
        heappush(heap,(1,v))
    order = []
    while heap:
        value,v = heappop(heap)
        if settled[v] or distance[v] != value: continue
        settled[v]=True
        order.append(v)
        for h in incidence[v]:
            remaining[h]-=1
            if remaining[h]: continue
            o,u,target,crossing,orientation = hyperarcs[h]
            candidate = distance[u]+2*distance[o]
            if not settled[target] and (distance[target] is None or candidate < distance[target]):
                distance[target]=candidate
                parent[target]=(crossing,orientation)
                heappush(heap,(candidate,target))
    return dict(degrees=distance, parents=parent, order=order, seeds=sorted(seeds))


def verify_profile(n, crossings, certificate):
    """Verify an optimality certificate by witnesses and Bellman inequalities.

    Finite labels have an acyclic attainment witness. Every enabled rule must
    satisfy d_target <= d_source+2*d_over. Unreached targets cannot have two
    reached dependencies. These conditions jointly prove fixed-seed optimality.
    """
    try:
        raw_seeds = certificate['seeds']
        seeds = set(raw_seeds)
        if len(seeds) != len(raw_seeds):return False
        validate(n,crossings,seeds)
        d, parents, order = certificate['degrees'], certificate['parents'], certificate['order']
        if len(d)!=n or len(parents)!=n or len(set(order))!=len(order): return False
        if any(x is not None and (type(x) is not int or x<1) for x in d): return False
        if set(order)!={i for i,x in enumerate(d) if x is not None}: return False
        seen = set()
        for target in order:
            if target in seeds:
                if d[target]!=1 or parents[target] is not None: return False
            else:
                i,orientation = parents[target]
                if not 0 <= i < len(crossings) or orientation not in (-1,1): return False
                o,u,v,_ = crossings[i]
                source,dest = (u,v) if orientation==1 else (v,u)
                if dest!=target or source not in seen or o not in seen: return False
                if d[target]!=d[source]+2*d[o]: return False
            seen.add(target)
        if not seeds <= seen: return False
        for o,u,v,_ in crossings:
            for source,target in ((u,v),(v,u)):
                if d[o] is not None and d[source] is not None:
                    if d[target] is None or d[target]>d[source]+2*d[o]: return False
        return True
    except (KeyError,TypeError,ValueError,IndexError):
        return False


def compile_seeds(n, crossings, certificate, *, label='fixed-seed Wirtinger presentation'):
    """Replace every arc by its certified seed expression; preserve ALL relations.

    Meridian status is relative to the input Wirtinger data. A production caller
    must have already certified that data came from its validated knot diagram.
    """
    if not verify_profile(n,crossings,certificate):
        raise ValueError('invalid fixed-seed certificate')
    if any(d is None for d in certificate['degrees']):
        raise ValueError('seeds do not generate all arcs by these rules')
    arena = Arena()
    seeds = certificate['seeds']
    values = {v:arena.letter(i+1) for i,v in enumerate(seeds)}
    for target in certificate['order']:
        if target in values: continue
        i,orientation = certificate['parents'][target]
        o,u,v,e = crossings[i]
        source = u if orientation==1 else v
        c = values[o] if e*orientation==1 else arena.inverse(values[o])
        values[target] = arena.concat(arena.concat(c,values[source]),arena.inverse(c))
    pairs = []
    for o,u,v,e in crossings:
        c = values[o] if e==1 else arena.inverse(values[o])
        lhs = arena.concat(arena.concat(c,values[u]),arena.inverse(c))
        pairs.append((lhs,values[v]))
    return arena.presentation(len(seeds),pairs,meridians=True,label=label)


def find_small_seeds(n, crossings, *, max_rank=2, max_attempts=10000, check=lambda: None):
    """Exhaust fixed seed sets up to size two. NOT_FOUND is not a knot verdict.

    A successful certificate is replayable by verify_profile. A production
    adapter must share its caller's deadline/work budget rather than silently
    starting a new full allowance for each call.
    """
    from itertools import combinations
    if max_rank not in (1,2):raise ValueError('this bounded search supports rank one or two')
    if type(max_attempts) is not int or max_attempts<0:raise ValueError('invalid attempt cap')
    validate(n,crossings,{0})
    attempts=0
    for rank in range(1,min(n,max_rank)+1):
        for seeds in combinations(range(n),rank):
            check()
            if attempts>=max_attempts:
                return dict(status='UNKNOWN',attempts=attempts,reason='seed-set attempt cap')
            attempts+=1
            certificate=minimum_degrees(n,crossings,seeds)
            if None not in certificate['degrees']:
                assert verify_profile(n,crossings,certificate)
                return dict(status='FOUND',rank=rank,attempts=attempts,certificate=certificate)
    return dict(status='NOT_FOUND',attempts=attempts,scope='no conclusion about knot type')
