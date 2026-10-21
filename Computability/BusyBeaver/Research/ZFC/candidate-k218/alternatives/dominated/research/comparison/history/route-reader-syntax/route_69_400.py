"""Focused finite local route census for only the 69/400 fold.
All candidates use one replacement row and existing table rows. A successful
route must restore every bit and reach the original one-step endpoint without
leaving the finite window. This is a local sufficient test, not runtime proof.
"""
from pathlib import Path
import itertools,json,hashlib,collections
A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20/binary/machine/k218.native.tm');O=Path(__file__).parent
T={}
for l in A.read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
states=sorted({q for q,b in T}-{400});radius=3;fuel=31
patterns=[]
for m in (0,1):
 for bits in itertools.product((0,1),repeat=5):
  xs=dict(zip((-3,-2,1,2,3),bits));xs[-1]=m;xs[0]=0
  patterns.append((m,sum(b<<(i+radius)for i,b in xs.items())))
base={(q,b):(w,d,69 if z==400 else z)for(q,b),(w,d,z)in T.items()if q!=400}
survivors=[];fail_counts=collections.Counter();prefix_best=[]
for action in itertools.product((0,1),(-1,1),states):
 table=base|{(69,0):action};passed=0;proof=[]
 for m,tape in patterns:
  original=tape;q,h=69,0;trace=[];reason='bound'
  for tick in range(fuel+1):
   if h==1 and q==(105 if m else104)and tape==original:
    reason='pass';break
   if not-radius<=h<=radius:reason='window';break
   if tick==fuel:break
   b=(tape>>(h+radius))&1
   if(q,b)not in table:reason='undefined';break
   w,d,z=table[q,b];trace.append([q,h,b,w,d,z])
   tape=(tape|1<<(h+radius))if w else(tape&~(1<<(h+radius)))
   q,h=z,h+d
  if reason!='pass':fail_counts[reason]+=1;break
  passed+=1;proof.append(trace)
 if passed:prefix_best.append({'action':action,'passed':passed})
 if passed==len(patterns):survivors.append({'action':action,'traces':proof})
out={'status':'FOCUSED_LOCAL_CENSUS_COMPLETE','table':str(A),'table_sha256':hashlib.sha256(A.read_bytes()).hexdigest(),'pair':[69,400],'replacement_row':[69,0],'redirects':{'400':69},'unchanged_common_row':[69,1,1,1,31],'radius':radius,'fuel':fuel,'patterns':len(patterns),'actions':4*len(states),'survivors':survivors,'fail_counts':dict(fail_counts),'partial_passes':sorted(prefix_best,key=lambda x:-x['passed'])[:20],'scope':'Only one-row 69/400 local route under arbitrary 7-cell windows with fixed predecessor marker and current0; not complete search, source calibration, initialization, or primitive runtime acceptance.'}
(O/'route-69-400.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='survivors'},indent=2));print('survivors',len(survivors))
