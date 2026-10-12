"""Count-only reference for the previous first-return strategy.

It recovers matching plus zero/positive bits, not physical gap lengths.
Calls are recomputed without caches, so timing compares complete independent
query compilation. This is not a copy of the earlier delivered implementation.
"""
from moment_kernel import Pairing, assemble_kernel


def compile_coning(size,pairings,terminals,edge_mass,port_owners,boundary_counts,oracle,
                   vertex_pairs=()):
    del edge_mass
    if not terminals:return assemble_kernel((),port_owners,boundary_counts,0),0
    calls=0
    def count(pairs,points=()):
        nonlocal calls
        extra=[]
        if points:
            h=points[0]
            extra=[Pairing(h,h,x,x) for x in points[1:]]
        calls+=1
        return sum(n for _,n in oracle(size,list(pairs)+extra,[],1))
    base=count(pairings);vbase=None;remaining=list(range(1,len(terminals)+1));result=[]
    def point(label):return terminals[label-1]
    while remaining:
        x=remaining[0];candidates=remaining[1:]
        while len(candidates)>1:
            half=candidates[:len(candidates)//2]
            c=count(pairings,[point(z) for z in half])
            cx=count(pairings,[point(z) for z in half]+[point(x)])
            if cx==c:candidates=half
            elif cx==c-1:candidates=candidates[len(candidates)//2:]
            else:raise ValueError('inconsistent count oracle')
        y=candidates[0]
        if count(pairings,[point(x),point(y)])!=base:raise ValueError('not an actual pair')
        if point(x)==point(y):length=0
        else:
            if vbase is None:vbase=count(vertex_pairs)
            length=int(count(vertex_pairs,[point(x),point(y)])!=vbase)
        result.append((min(x,y),max(x,y),length));remaining.remove(x);remaining.remove(y)
    return assemble_kernel(tuple(sorted(result)),port_owners,boundary_counts,calls),calls
