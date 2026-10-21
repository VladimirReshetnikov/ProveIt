"""Own static equality join over existing rows, not a machine simulation/search.
Looks only for exact three-step left-marker multiplexers for opposite-marker
source decoder roles having one identical branch. Incoming edges are checked
separately; a found algebraic gadget is not automatically a global quotient.
"""
from pathlib import Path
import json,itertools
O=Path(__file__).parent;D=json.loads((O/'roles.json').read_text());T={}
for l in Path(D['table_sha256'] if False else '/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20/binary/machine/k218.native.tm').read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
answers=[];pairs=[]
for row in D['one_equal_branch_pairs']:
 q,r=row['pair'];suffix=row['suffixes']
 if suffix not in [[['0'],['1']],[['1'],['0']]]:continue
 b=1-row['same'][0];targets={int(suffix[i][0]):tuple(row['rows'][i][b])for i in(0,1)}
 if any(a[:2]!=(b,1)for a in targets.values()):continue
 pairs.append([q,r]);incoming_ok=all(all(w==int(suffix[i][0])and d==1 for _,_,w,d in D['roles'][str(s)]['incoming'])for i,s in enumerate((q,r)))
 for h in sorted({s for s,b in T}):
  legs=[]
  for m in(0,1):
   w,d,k=T[h,m]
   if(w,d)!=(m,1)or T.get((k,b))!=targets[m]:break
   legs.append([h,m,w,d,k,k,b,*targets[m]])
  else:answers.append({'pair':[q,r],'different_branch':b,'markers':suffix,'helper':h,'legs':legs,'incoming_marker_sufficient':incoming_ok,'caveat':'Need choose retained q and check gadget avoids modified/deleted rows, current proofs and initialization before any acceptance.'})
out={'status':'STATIC_THREE_STEP_ROW_JOIN_COMPLETE','eligible_opposite_marker_direct_pairs':len(pairs),'pairs':pairs,'gadgets':answers,'table_sha256':D['table_sha256'],'scope':'Exact three-step shape only; no larger synthesis or lower bound.'}
(O/'three-step-gadgets.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
