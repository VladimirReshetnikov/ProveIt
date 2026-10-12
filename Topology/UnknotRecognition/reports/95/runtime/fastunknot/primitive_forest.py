"""Raw unit-coordinate primitive forests; source provenance is required.

A primitive root with child coordinate +/-1 solves that generator as an
integer power of its parent. Acyclic dependencies permit one simultaneous
substitution even when donors overlap. Other primitive pairs are excluded.
"""
from math import gcd
from .primitive_projection import projection_candidates
from .primitive_power import primitive_power_terminal


def plan_forest(arena, roots, alive, cache=None, *, _prepared=None, _power=None):
    if cache is None:cache = {}
    candidates,powers = projection_candidates(arena,roots,alive,cache) if _prepared is None else _prepared
    vectors=cache.setdefault('forest_vectors',{})
    components={};sizes={}
    used=set();edges=[]
    def find(g):
        if g not in components:
            arena.tick();components[g]=g;sizes[g]=1
        while components[g]!=g:
            arena.tick();components[g]=components[components[g]];g=components[g]
        return g
    for slot,root,(pair,raw_vector) in candidates:
        arena.tick()
        if root not in vectors:
            u,v=raw_vector;d=gcd(abs(u),abs(v));u//=d;v//=d
            vectors[root]=(u,v,d) if min(abs(u),abs(v))==1 else None
        if vectors[root] is None:continue
        a,b=pair;u,v,d=vectors[root]
        choices=[g for g,k in zip(pair,(u,v)) if abs(k)==1 and g not in used]
        if not choices:continue
        left,right=find(a),find(b)
        if left==right:continue
        if root not in powers:
            if d==1:
                # A coherent word containing one occurrence of one generator
                # is a cyclic conjugate of a power of the other followed by it.
                powers[root]=dict(kind='rank_two_primitive_power',relation=0,
                    generators=list(pair),primitive_vector=[u,v],exponent=1,width=abs(u)+abs(v)-1)
            else:
                powers[root]=(_power or primitive_power_terminal)(arena,[root],set(pair))
        if powers[root] is None:continue
        child=max(choices)
        edges.append(dict(child=child,proof=dict(powers[root],relation=slot)))
        used.add(child)
        if sizes[left]<sizes[right]:left,right=right,left
        components[right]=left;sizes[left]+=sizes[right]
    arena.stats['forest_attempts']=arena.stats.get('forest_attempts',0)+1
    return edges


def apply_forest(arena, roots, alive, edges):
    """Apply internally proved edges; do not call this on unverified input."""
    parents={}
    for edge in edges:
        arena.tick();child=edge['child'];proof=edge['proof']
        a,b=proof['generators'];u,v=proof['primitive_vector']
        parents[child]=(b,-v*u) if child==a else (a,-u*v)
    finished={g for g in alive if g not in parents};order=[]
    for child in parents:
        chain=[];node=child
        while node not in finished:
            arena.tick();chain.append(node);node=parents[node][0]
        for node in reversed(chain):
            arena.tick();finished.add(node);order.append(node)
    images={}
    for child in order:
        arena.tick();parent,exponent=parents[child]
        if parent not in images:
            images[parent]=arena.letter(parent);images[-parent]=arena.letter(-parent)
        positive,negative=(images[parent],images[-parent]) if exponent>0 else (images[-parent],images[parent])
        # Reuse the parent's circuit instead of re-encoding the full product of
        # path exponents. The powering loop sees only this edge's exponent.
        images[child]=arena.power(positive,abs(exponent))
        images[-child]=arena.power(negative,abs(exponent))
    mapped={0:0}
    for node in arena._reachable(roots):
        arena.tick();rule=arena.rules[node]
        mapped[node]=images.get(rule[1],node) if rule[0]=='t' else arena.concat(mapped[rule[1]],mapped[rule[2]])
    roots[:]=[mapped[r] for r in roots]
    for edge in edges:
        arena.tick();roots[edge['proof']['relation']]=0;alive.remove(edge['child'])
    arena.stats['forest_rounds']=arena.stats.get('forest_rounds',0)+1
    arena.stats['forest_edges']=arena.stats.get('forest_edges',0)+len(edges)
