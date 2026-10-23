"""Independent aggregate-clause audit; proof uses an interval, not these samples."""
import json,random
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=root/'native/source/coefficients__wang943_tiles.json'
data=json.loads(p.read_text());tiles=data.get('tiles',data) if isinstance(data,dict) else data
if isinstance(tiles,dict):tiles=list(tiles.values())
widths=[9,10,9,10];old_starts=[0,9,19,28];perm=list(range(8))+[34]+list(range(8,17))+[35]+list(range(17,25))+[36]+list(range(25,34))+[37]+[38,39,40]
Q=1<<41;mask=(1<<51)-2;rng=random.Random(943);count=0
assert len(tiles)==943
for tile in tiles:
 v=sum(1<<perm[old_starts[s]+j] for s in range(4) for j in range(widths[s]) if (tile[s]+(1<<(widths[s]-1)))>>j&1)+sum(1<<j for j in [38,39,40])
 assert v>>34==127
 c=1+1024*(Q-v)
 cases={0,Q-1,v,*[rng.randrange(Q) for _ in range(64)]}
 for j in range(41):
  for sign in [-1,1]:
   u=v+sign*(1<<j)
   if 0<=u<Q:cases.add(u)
 for W in cases:
  assert ((c+1024*W)&mask==0)==(W==v)
  count+=1
assert [n for n in range(944) if n&1022==0]==[0,1]
for W in [0,Q-1]+[1<<j for j in range(41)]:
 assert ((1024*W)&mask==0)==(W==0)
result={'tiles':943,'payload_assignments':count,'selector_counts':944,'empty_boundary_tests':43,'status':'PASS','proof_scope':'Complete decoder follows from n<1024 and 0<2^41-v+W<2^42, not exhaustive testing of W.'}
Path(__file__).with_name('complement_clause_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
