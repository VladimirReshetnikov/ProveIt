from pathlib import Path
import sys,json,time,itertools
from environment import P as PORTABLE, BASE_SOURCE, BASE_TABLE
import argparse
P=PORTABLE.parent;import build221 as b
sys.path.insert(0,str(PORTABLE/'runtime/vendor'));import symbolic_runtime as r
ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();OUT=args.out;OUT.mkdir(parents=True,exist_ok=True)
T=b.read_table(BASE_TABLE.read_bytes());S=json.loads(BASE_SOURCE.read_text());m={int(k):int(v)for k,v in json.loads((P/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()};m.update({q:q+1000 for q in {q for q,c in T}if q not in m})
L={(m[q],c):(w,d,m[z])for(q,c),(w,d,z)in T.items()if q!=198};lemmas,blocks=r.prove_blocks(L);Q=sorted({q for q,b in T}-{198});count=0;hits=[];passcd=[];start=time.monotonic()
for w,d,q in itertools.product((0,1),(-1,1),Q):
 count+=1;L[m[66],0]=(w,d,m[q])
 try:r.case(L,lemmas,S[0],False)
 except Exception:continue
 act=(w,d,q);print('CD0_PASS',act,'n',count,'sec',round(time.monotonic()-start,1),flush=True);passcd.append(act)
 for append in range(5):
  try:
   r.case(L,lemmas,S[0],True,append=append)
   r.case(L,lemmas,S[3],False,append=append)
  except Exception:continue
  rec={'action':act,'append':append};hits.append(rec);N={k:v for k,v in T.items()if k[0]!=198};N[66,0]=act
  (OUT/f'hit{len(hits)}.tm').write_bytes(b.table_bytes(N));print('HIT',rec,flush=True)
result={'tested':count,'passes_zero_decrement':passcd,'hits':hits,'seconds':time.monotonic()-start};(OUT/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
