import json,math,itertools,time
from pathlib import Path
root=Path(__file__).parent
base=json.loads((root/'bose_chowla_31.json').read_text()); M=base['group_order']; w=base['weights_with_zero']
best=(M,0,0,None)
for k in range(1,M//2+1):
 if math.gcd(k,M)!=1:continue
 a=sorted((k*x)%M for x in w)
 gap,idx=max(((a[(i+1)%32]-a[i])%M,i) for i in range(32))
 width=M-gap
 if width<best[0]:
  b=a[(idx+1)%32];bweights=sorted((x-b)%M for x in a)
  best=(width,k,b,bweights)
seen=set()
for tup in itertools.combinations_with_replacement(best[3],4):
 s=sum(tup)%M;assert s not in seen;seen.add(s)
out={'modulus':M,'multiplier':best[1],'translation_after_multiplier':best[2],'max_weight':best[0],'weights_with_zero':best[3],'witness_weights':best[3][1:],'four_multisets_checked':len(seen),'search_scope':'All unit multipliers 1 through floor(M/2), all cyclic rotations; not all B4 sets.'}
(root/'bose_chowla_31_optimized.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
