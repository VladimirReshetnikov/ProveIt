"""Exhaustive exposed literal donor scan (quadratic in reduced input letters).

No group assertion is made without source replay and the knot-group hypothesis.
The list is deduplicated by exact edge data. Compact certificates refer to the
source relator slot, its repeated-root length, a rotation and two cut positions.
"""
from words import cyclic_reduce, primitive_period, inverse
from power_graph import Edge

def extract(relators):
    result=[]; proofs=[]; seen=set()
    def add(edge,proof):
        key=(edge.s,edge.t,edge.a,edge.b,edge.plain)
        if key not in seen: seen.add(key); result.append(edge); proofs.append(proof)
    for slot,word in enumerate(relators):
        R=cyclic_reduce(word)
        if not R: continue
        p=primitive_period(R); root=R[:p]
        if all(x==root[0] for x in root):
            g=abs(root[0]); add(Edge(g,g,2,1,True),{'kind':'power','slot':slot})
            continue
        for rot in range(p):
            # Only the beginning of a maximal cyclic signed-letter run.
            if root[rot]==root[rot-1]: continue
            w=root[rot:]+root[:rot]
            head=1
            while head<p and w[head]==w[0]: head+=1
            # LCP of candidate conjugator with inverse suffix. All possible
            # k <= lcp satisfy W^{-1} = last k letters, without copying W.
            iw=inverse(w); lcp=0
            while head+lcp<p and lcp<p and w[head+lcp]==iw[lcp]: lcp+=1
            ends=[0]*p; ends[-1]=p
            for z in range(p-2,-1,-1): ends[z]=ends[z+1] if w[z]==w[z+1] else z+1
            for k in range(min(lcp,(p-head-1)//2)+1):
                begin=head+k; count=p-head-2*k
                if count<=0 or ends[begin]<begin+count: continue
                x,y=w[0],w[begin]
                edge=Edge(abs(x),abs(y),(1 if x>0 else -1)*head,
                          -(1 if y>0 else -1)*count,k==0)
                add(edge,{'kind':'conjugacy','slot':slot,'period':p,
                          'rotation':rot,'head':head,'conj':k})
    return result,proofs
