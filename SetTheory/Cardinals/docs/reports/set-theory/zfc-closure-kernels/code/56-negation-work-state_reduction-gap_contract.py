"""Observation of a complete affine frame modulo its unused zero gap.

The marker and every represented non-gap cell remain exact. A gap with affine
length a*n+c is accepted only when a>=0 and its minimum makes the header at
least 40 cells from the dispatch head. Ordinary canonical zero-padding means
trailing zero PC bits belong to that gap. This is a sufficient universal
endpoint relation, not finite sampling over n.
"""

def generalized_canon(original_canon):
    def observe(left,right):
        l,r=original_canon(left,right)
        if len(r)<3 or r[-1][0]!='box' or r[-2]!=(1,0,1):return l,r
        gap=r[-3]
        if len(gap)!=3 or gap[0]!=0:return l,r
        prefix=r[:-3]
        if any(len(seg)!=3 or seg[0] not in (0,1) or seg[1]!=0 for seg in prefix):
            return l,r
        prefix_length=sum(seg[2] for seg in prefix)
        _,a,c=gap
        if a>=0 and c+prefix_length>=40:
            r=prefix+((0,'gap_at_least',40-prefix_length),)+r[-2:]
        return l,r
    return observe
