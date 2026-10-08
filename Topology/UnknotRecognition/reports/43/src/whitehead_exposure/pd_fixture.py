"""Validated connected planar PD fixture loader, for isolated group-stage audits.

Uses the upstream odd-slot overpass convention. This is a source-derived
frontend, not a replacement for the maintained Diagram class.
"""
from collections import defaultdict
from .algebra import cyclic_reduce


def presentation_from_pd(pd):
    if type(pd) is not list or not pd:
        raise ValueError('nonempty connected PD required')
    positions=defaultdict(list)
    n=len(pd)
    for i,row in enumerate(pd):
        if type(row) is not list or len(row)!=4 or any(type(x) is not int or x<0 for x in row):
            raise ValueError('invalid PD row')
        for j,label in enumerate(row): positions[label].append(4*i+j)
    if len(positions)!=2*n or any(len(v)!=2 for v in positions.values()):
        raise ValueError('each arc must occur twice')
    mate={}
    for a,b in positions.values(): mate[a]=b;mate[b]=a
    # Connected ribbon graph plus Euler characteristic 2 certifies genus zero.
    vertices={0}; pending=[0]
    while pending:
        v=pending.pop()
        for j in range(4):
            w=mate[4*v+j]//4
            if w not in vertices: vertices.add(w);pending.append(w)
    if len(vertices)!=n: raise ValueError('PD projection not connected')
    seen=set();faces=0
    for d in range(4*n):
        if d in seen: continue
        faces+=1
        while d not in seen:
            seen.add(d); e=mate[d]; d=4*(e//4)+(e+1)%4
    if faces!=n+2: raise ValueError('PD rotation system has nonzero genus')
    incoming=[set() for _ in pd]; d=0; visited=set()
    while d not in visited:
        visited.add(d); incoming[d//4].add(d%4)
        d=mate[4*(d//4)+(d+2)%4]
    if d!=0 or len(visited)!=2*n: raise ValueError('PD is not one-component')
    adjacency={label:set() for label in positions}
    for row in pd:
        adjacency[row[1]].add(row[3]); adjacency[row[3]].add(row[1])
    owner={}; count=0
    for g in sorted(adjacency):
        if g in owner: continue
        count+=1;owner[g]=count;pending=[g]
        while pending:
            for h in adjacency[pending.pop()]:
                if h not in owner:owner[h]=count;pending.append(h)
    words=[]
    for row,ports in zip(pd,incoming):
        under=ports&{0,2};over=ports&{1,3}
        if len(under)!=1 or len(over)!=1: raise ValueError('invalid oriented crossing')
        u,o=under.pop(),over.pop()
        left,right,top=owner[row[u]],owner[row[(u+2)%4]],owner[row[o]]
        if (o-u)%4==1:left,right=right,left
        words.append(cyclic_reduce((top,left,-top,-right)))
    return words, tuple(range(1,count+1)), {'crossings':n,'faces':faces,'components':1}
