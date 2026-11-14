from pathlib import Path
from history_search import read,histories,finite,exact
import json,random,time,sys
p=Path(__file__).parent; t=read(sys.argv[1]); ctx,cnt=histories(t,12); rng=random.Random(20261029);Q=sorted({q for q,b in t});out=[]; st=time.time(); trials=0
for q in Q:
 for b in (0,1):
  for z in Q+[254]:
   for w in (0,1):
    for d in (-1,1):
     a=(w,d,z)
     if a==t[q,b]:continue
     trials+=1; nt=dict(t);nt[q,b]=a
     if not all(finite(t,nt,q,q,c,b,rng,40) for c in ctx[q] for _ in range(2)):continue
     cs=[]
     for c in ctx[q]:
      ex=exact(t,nt,q,q,c,b,40)
      if ex is None:break
      cs.append({'context':c,'cases':ex})
     else:
      out.append({'row':[q,b,*a],'cert':cs});print('REWRITE',q,b,a,flush=True)
 if q%10==0:print('progress',q,len(out),time.time()-st,flush=True)
(p/'neutral.json').write_text(json.dumps({'input':sys.argv[1],'depth':12,'limit':40,'trials':trials,'rewrites':out,'seconds':time.time()-st},indent=2))
