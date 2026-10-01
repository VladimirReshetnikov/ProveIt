"""Exact independent six-edge orbit census with shores kept distinct."""
from itertools import permutations
import json
from pathlib import Path
perms=list(permutations(range(3)))
def transform(mask,rp,cp):
    return sum(1<<(3*rp[i]+cp[j]) for i in range(3) for j in range(3) if mask&(1<<(3*i+j)))
def canonical(mask):return min(transform(mask,r,c) for r in perms for c in perms)
orbits={}
for mask in range(512):
    if mask.bit_count()==6:orbits.setdefault(canonical(mask),[]).append(mask)
expected=[63,95,119,219,221,238]
if sorted(orbits)!=expected:raise RuntimeError(orbits)
result={'six_edge_masks':sum(map(len,orbits.values())), 'canonical_orbits':sorted(orbits), 'orbit_sizes':{str(k):len(v) for k,v in sorted(orbits.items())},'transpose_identification_used':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
