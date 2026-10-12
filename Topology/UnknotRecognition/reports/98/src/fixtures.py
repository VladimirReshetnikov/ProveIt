"""Deterministic fixtures and small-source generators."""
from __future__ import annotations
import random
from reference import expand, ExpansionLimit

def leaf(n,edges,terminals=()):
    return {"op":"leaf","vertices":list(range(n)),"edges":[list(e) for e in edges],"terminals":list(terminals)}

def mapping(child,mp,keep):
    return {"op":"map","children":[child],"maps":[list(mp)],"keep":list(keep)}

def joining(left,right,mpa,mpb,keep):
    return {"op":"join","children":[left,right],"maps":[list(mpa),list(mpb)],"keep":list(keep)}

def k4(k=3):
    return {"k":k,"nodes":[leaf(4,[(u,v,1) for u in range(4) for v in range(u+1,4)])]}

def prism(k=3):
    edges=[(0,1,1),(1,2,1),(2,0,1),(3,4,1),(4,5,1),(5,3,1),(0,3,1),(1,4,1),(2,5,1)]
    return {"k":k,"nodes":[leaf(6,edges)]}

def component_fan(c: int,k: int=3,retain: bool=False):
    """c heavy edges each with one terminal; finally identify all roots.

Closed output is a star, while the preceding interface has c free components.
"""
    if c<1: raise ValueError("positive component count required")
    nodes=[leaf(2,[(0,1,k+1)],[0])]
    for j in range(1,c): nodes.append(joining(len(nodes)-1,0,range(j),[j],range(j+1)))
    if not retain: nodes.append(mapping(len(nodes)-1,[0]*c,[]))
    return {"k":k,"nodes":nodes}

def hidden_power(depth: int,k: int=3):
    nodes=[leaf(2,[(0,1,1)],[])]
    for _ in range(depth):
        j=len(nodes)-1; nodes.append(joining(j,j,[],[],[]))
    return {"k":k,"nodes":nodes}

def permutation_power(width: int,depth: int,k: int=3,capacity: int=1):
    """Fresh serial doubling of w disjoint permuted channels, then close."""
    nodes=[leaf(2*width,[(j,width+(j+1)%width,capacity) for j in range(width)],range(2*width))]
    for _ in range(depth):
        j=len(nodes)-1
        nodes.append(joining(j,j,range(2*width),list(range(width,2*width))+list(range(2*width,3*width)),
                             list(range(width))+list(range(2*width,3*width))))
    nodes.append(mapping(len(nodes)-1,list(range(width))*2,[]))
    return {"k":k,"nodes":nodes}

def random_grammar(rng: random.Random,k: int=3,steps: int=7):
    nodes=[]; widths=[]
    for _ in range(2):
        n=rng.randrange(0,5); es=[]
        if n:
            for _ in range(rng.randrange(0,7)):
                es.append((rng.randrange(n),rng.randrange(n),rng.randrange(1,6)))
        ts=[v for v in range(n) if rng.randrange(2)]; rng.shuffle(ts)
        nodes.append(leaf(n,es,ts)); widths.append(len(ts))
    for _ in range(steps):
        arity=rng.choice([1,2]); ch=[rng.randrange(len(nodes)) for _ in range(arity)]
        total=sum(widths[c] for c in ch); labels=[]; nextid=0
        for j in range(total):
            if nextid and rng.random()<0.45: labels.append(rng.randrange(nextid))
            else: labels.append(nextid); nextid+=1
        keep=[q for q in range(nextid) if rng.random()<0.65]; rng.shuffle(keep)
        maps=[]; off=0
        for c in ch: maps.append(labels[off:off+widths[c]]); off+=widths[c]
        z={"op":"map" if arity==1 else "join","children":ch,"maps":maps,"keep":keep}
        trial={"k":k,"nodes":nodes+[z]}
        try: expand(trial,max_vertices=10,max_edges=45)
        except ExpansionLimit: continue
        nodes.append(z); widths.append(len(keep))
    return {"k":k,"nodes":nodes}
