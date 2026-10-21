import json,itertools,time
from pathlib import Path
start=time.time();H=Path(__file__).resolve().parent
for up in [(3,2,4),(1,2,12,8),(7,6,4,8),(3,2,12,8),(15,14,12,8)]:
 n=len(up);top=(1<<n)-1;U=[a for a in range(1<<n)if all(not(a>>i&1)or up[i]&~a==0 for i in range(n))]
 neg={a:sum(1<<i for i in range(n)if not(up[i]&a))for a in U};regular=[a for a in U if neg[neg[a]]==a];maps=[]
 for sets in itertools.product(U[1:],repeat=n):
  if any((up[i]>>j&1)and(sets[j]&~sets[i])for i in range(n)for j in range(n)):continue
  q={a:sum(1<<i for i in range(n)if sets[i]&~a==0)for a in U}
  if any(neg[q[neg[q[a]]]]&~a for a in U):continue
  maps.append((sets,q))
 print('poset',up,'algebra',len(U),'maps',len(maps),'secs',round(time.time()-start,2),flush=True)
 for x,y in itertools.combinations_with_replacement(maps,2):
  S,q=x;T,r=y
  if any(q[r[a]]!=r[q[a]]for a in U):continue
  for a in regular:
   qr=neg[neg[q[neg[neg[r[a]]]]]];rq=neg[neg[r[neg[neg[q[a]]]]]]
   if qr!=rq:
    d={'up':up,'upsets':U,'S':S,'T':T,'Q':q,'R':r,'witness':a,'NNQNNR':qr,'NNRNNQ':rq};print('COUNTERMODEL',d,flush=True);(H/'booleanized_commutation_countermodel.json').write_text(json.dumps(d,indent=2)+'\n');raise SystemExit
print('No countermodel in tested posets')
