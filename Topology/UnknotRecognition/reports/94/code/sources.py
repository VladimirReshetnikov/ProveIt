"""Genuine regular-cell sources and independent finite source oracles.

The product source is a modularly indexed path times a finite simplicial
complex. It is a PL 3-ball when the base is a triangulated disk and gcd=1.
These sources are not claimed to be an adapter to ProveIt's normal-cut schema.
"""
from __future__ import annotations
from itertools import combinations
from collections import defaultdict, deque
from math import gcd
from ranked_morse import (Family,Cover,Match,Packet,prepare,expand,solve_offsets,
                          synthesize_affine,synthesize_modular)


def simplex_faces(facets):
    cells = set()
    for facet in facets:
        facet = tuple(sorted(facet))
        if not facet or len(set(facet)) != len(facet):
            raise ValueError('invalid simplex')
        for k in range(1,len(facet)+1):
            cells.update(combinations(facet,k))
    return tuple(sorted(cells,key=lambda x:(len(x),x)))


def base_covers(cells):
    return tuple((s,s[:k]+s[k+1:]) for s in cells if len(s)>1 for k in range(len(s)))


def greedy_base_matching(cells):
    """Ordinary explicit free-face collapse, only on the small base."""
    alive = set(cells)
    covers = base_covers(cells)
    parents = {s:set() for s in cells}
    faces = {s:set() for s in cells}
    for s,t in covers:
        parents[t].add(s); faces[s].add(t)
    matches = []
    while True:
        choice = None
        for s in sorted(alive,key=lambda x:(-len(x),x)):
            if parents[s]:
                continue
            for t in sorted(faces[s]):
                if parents[t] == {s}:
                    choice = s,t; break
            if choice:
                break
        if choice is None:
            return tuple(matches),tuple(sorted(alive))
        s,t = choice
        matches.append((s,t)); alive.remove(s); alive.remove(t)
        for f in faces[s]:
            parents[f].discard(s)
        for f in faces[t]:
            parents[f].discard(t)


def disk_fan(n: int):
    if n < 3:
        raise ValueError('fan requires at least three boundary vertices')
    return tuple((0,i+1,(i+1)%n+1) for i in range(n))


def surface_is_disk(facets) -> bool:
    """Validate connected compact triangulated surface, boundary, and chi=1.

    Connected vertex links are cycles or intervals. The classification of
    compact surfaces then implies this is a disk. No supplied flag is trusted.
    """
    try:
        facets = tuple(tuple(sorted(f)) for f in facets)
        if not facets or any(len(f)!=3 or len(set(f))!=3 for f in facets) or len(set(facets))!=len(facets):
            return False
        cells = simplex_faces(facets)
        vertices = [s[0] for s in cells if len(s)==1]
        edges = [s for s in cells if len(s)==2]
        degree = {e:sum(set(e).issubset(t) for t in facets) for e in edges}
        if any(d not in (1,2) for d in degree.values()) or not any(d==1 for d in degree.values()):
            return False
        adj = defaultdict(set)
        for a,b in edges:
            adj[a].add(b); adj[b].add(a)
        def connected(graph):
            if not graph: return False
            seen=set(); queue=[next(iter(graph))]
            while queue:
                v=queue.pop()
                if v not in seen:
                    seen.add(v); queue.extend(graph[v]-seen)
            return len(seen)==len(graph)
        if not connected(adj): return False
        for v in vertices:
            link=defaultdict(set)
            for t in facets:
                if v in t:
                    a,b=[x for x in t if x!=v]
                    link[a].add(b);link[b].add(a)
            ds=[len(x) for x in link.values()]
            if not connected(link) or any(d not in (1,2) for d in ds) or ds.count(1) not in (0,2):
                return False
        return len(vertices)-len(edges)+len(facets)==1
    except (TypeError,ValueError):
        return False


def modular_path(N: int, step: int, start: int = 0, *, split_terminal: bool = False,
                 closed: bool = False):
    if type(N) is not int or type(step) is not int or type(start) is not int or N < 2 or not 1<=step<N or not 0<=start<N:
        raise ValueError('invalid modular path parameters')
    terminal=(start-step)%N
    if split_terminal:
        intervals=[('VL',0,terminal-1),('VT',terminal,terminal),('VR',terminal+1,N-1)]
    else:
        intervals=[('V',0,N-1)]
    vertices=[Family(name,0,a,b) for name,a,b in intervals if a<=b]
    edges = ([Family('EC',1,0,N-1)] if closed else
             [Family(name,1,a,b) for name,a,b in [('EL',0,terminal-1),('ER',terminal+1,N-1)] if a<=b])
    covers=[];matches=[]
    def add(e,lo,hi,shift,matched):
        for v in vertices:
            a,b=max(lo,v.lo-shift),min(hi,v.hi-shift)
            if a<=b:
                k=len(covers)
                covers.append(Cover(e.name,v.name,a,b,1,shift))
                if matched: matches.append(Match(k,a,b))
    for e in edges:
        add(e,e.lo,e.hi,0,True)
        lo,hi=e.lo,min(e.hi,N-step-1)
        if lo<=hi: add(e,lo,hi,step,False)
        lo,hi=max(e.lo,N-step),e.hi
        if lo<=hi: add(e,lo,hi,step-N,False)
    packet=Packet(tuple(vertices+edges),tuple(covers),tuple(matches))
    return packet,terminal


def path_proof(packet,N,step,start=0):
    if gcd(N,step)!=1:
        return None
    inverse=pow(step,-1,N)
    p=prepare(packet)
    a={f.name:-inverse for f in packet.families}
    c={f.name:inverse*start+N-1 for f in packet.families}
    return synthesize_modular(p,N,2,a,c)


def product_source(N,step,facets,start=0,base_matching=None):
    path,terminal=modular_path(N,step,start,split_terminal=True)
    cells=simplex_faces(facets)
    if base_matching is None:
        base_matching,_=greedy_base_matching(cells)
    ids={s:'.'.join(map(str,s)) for s in cells}
    name=lambda p,s:p+'|'+ids[s]
    families=[]; metadata={}
    for f in path.families:
        for s in cells:
            label=name(f.name,s)
            families.append(Family(label,f.dim+len(s)-1,f.lo,f.hi))
            metadata[label]=(f.dim,s)
    covers=[];matches=[]
    path_match=defaultdict(list)
    for m in path.matching:
        path_match[m.cover].append(m)
    for k,c in enumerate(path.covers):
        for s in cells:
            j=len(covers)
            covers.append(Cover(name(c.upper,s),name(c.lower,s),c.lo,c.hi,c.slope,c.shift))
            for m in path_match[k]:
                matches.append(Match(j,m.lo,m.hi))
    base_match=set(base_matching)
    for f in path.families:
        for s,t in base_covers(cells):
            j=len(covers)
            covers.append(Cover(name(f.name,s),name(f.name,t),f.lo,f.hi))
            if f.dim==0 and f.lo==f.hi==terminal and (s,t) in base_match:
                matches.append(Match(j,terminal,terminal))
    packet=Packet(tuple(families),tuple(covers),tuple(matches))
    return packet,metadata,tuple(base_matching)


def product_proof(packet,N,step,facets,start=0):
    if gcd(N,step)!=1:
        return None
    inverse=pow(step,-1,N)
    cells=simplex_faces(facets)
    a={f.name:-inverse for f in packet.families}
    c={f.name:inverse*start+N-1 for f in packet.families}
    return synthesize_modular(prepare(packet),N,2*len(cells)+4,a,c)


def independent_product_oracle(N,step,facets,start=0,base_matching=None):
    """Build geometry directly from path edges and simplex subsets (small N only).

    It does not inspect or expand the compressed packet and uses a different
    namespace: ((path dimension, source rank), base simplex).
    """
    if N>10000: raise ValueError('independent explicit source cap')
    terminal=(start-step)%N
    cells=simplex_faces(facets)
    if base_matching is None:
        base_matching,_=greedy_base_matching(cells)
    path_cells=[(0,i) for i in range(N)]+[(1,i) for i in range(N) if i!=terminal]
    dims={(p,s):p[0]+len(s)-1 for p in path_cells for s in cells}
    covers=set();matches=set()
    for p in path_cells:
        for s,t in base_covers(cells):
            pair=((p,s),(p,t));covers.add(pair)
            if p==(0,terminal) and (s,t) in base_matching:
                matches.add(pair)
        if p[0]==1:
            for s in cells:
                tail=(((1,p[1]),s),((0,p[1]),s))
                head=(((1,p[1]),s),((0,(p[1]+step)%N),s))
                covers.add(tail);covers.add(head);matches.add(tail)
    return dims,covers,matches


def compare_product_geometry(packet,metadata,N,step,facets,start=0,base_matching=None):
    dims,covers,matches=expand(prepare(packet))
    def key(x):
        family,index=x
        dim,s=metadata[family]
        return ((dim,index),s)
    mapped=({key(x):d for x,d in dims.items()},
            {(key(u),key(v)) for u,v in covers},
            {(key(u),key(v)) for u,v in matches})
    return mapped==independent_product_oracle(N,step,facets,start,base_matching)
