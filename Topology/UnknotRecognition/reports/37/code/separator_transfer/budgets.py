"""Sharp homology lower bounds from chain dimensions and differential rank caps."""
from __future__ import annotations
from collections import defaultdict
from typing import Mapping

def sharp_rank_budget(dimensions: Mapping[tuple[int,int],int],
                      capacities: Mapping[tuple[int,int],int]):
    """Maximize sum r[h,j], with r[h-1,j]+r[h,j]<=c[h,j], 0<=r<=cap.

    All quantities are exact binary integers. Leftmost-edge saturation is
    optimal for this unweighted capacitated path-matching problem. Large gaps
    in degree labels are not expanded.
    """
    for data in (dimensions,capacities):
        if any(len(key) != 2 or any(type(x) is not int for x in key) or type(v) is not int or v < 0
               for key,v in data.items()):
            raise ValueError("invalid graded dimensions or capacities")
    by_q = defaultdict(set)
    for h,j in dimensions: by_q[j].add(h)
    allocation = {}
    for j,hs in sorted(by_q.items()):
        for h in sorted(hs):
            r = min(capacities.get((h,j),0),
                    dimensions[h,j]-allocation.get((h-1,j),0),
                    dimensions.get((h+1,j),0))
            if r: allocation[h,j] = r
    maximum = sum(allocation.values())
    S = sum(dimensions.values())
    return {'dimension':S, 'maximum_rank_sum':maximum,
            'homology_lower':S-2*maximum, 'allocation':allocation,
            'unresolved_dimension_bound':2*maximum+1}
