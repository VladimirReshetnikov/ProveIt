from pathlib import Path
from history_search import read,histories,finite,exact
import json,random,time,collections,itertools
p=Path(__file__).parent;nr=json.loads((p/'compat_neutral.json').read_text());t=read(nr['input']);ctx,_=histories(t,12);Q=sorted({q for q,b in t});rng=random.Random(132535);nd=collections.defaultdict(list)
for rw in nr['rewrites']:
 h,b,w,d,z=rw['row'];nd[h,b].append((w,d,z))
def sample(q,r,c,b):
 if 0 in c and c[0]!=b:return None
 cs={i:rng.randrange(2)for i in range(-50,51)};cs.update(c);cs[0]=b
 w,d,z=t[q,b];z=r if z==q else z
 exp=dict(cs);exp[0]=w
 return cs,(z,d,exp)
def run(nt,r,sample):
 if sample is None:return True,set()
 cs,(z,d,exp)=sample;act=dict(cs);q=r;h=0;trace=set()
 for k in range(40):
  if q==254:return False,trace
  b=act[h];trace.add((q,b));w,dh,q=nt[q,b];act[h]=w;h+=dh
  if(q,h)==(z,d)and act==exp:return True,trace
 return False,trace
st=time.time();trials=0;repairs=0;found=[]
for i,q in enumerate(Q):
 for r in Q[:i]:
  if 0 in(q,r):continue
  for bit in(0,1):
   if t[q,1-bit]!=t[r,1-bit]:continue
   if any(z in(q,r)for w,d,z in[t[s,b]for s in(q,r)for b in(0,1)]):continue
   samples=[sample(s,r,c,b)for s in(q,r)for c in ctx[s]for b in(bit,1-bit)]
   nt={(s,b):(w,d,r if z==q else z)for(s,b),(w,d,z)in t.items()if s!=q}
   for z in Q:
    if z==q:continue
    for w,d in itertools.product((0,1),(-1,1)):
     trials+=1;nt[r,bit]=(w,d,z)
     for smp in samples:
      ok,trace=run(nt,r,smp)
      if not ok:break
     else:continue
     for hb in trace:
      h,hbit=hb
      if h in(q,r)or t[hb][2]==q:continue
      orig=nt[hb]
      for action in nd[hb]:
       if action[2]==q:continue
       repairs+=1;nt[hb]=action
       if not all(run(nt,r,sm)[0]for sm in samples):continue
       if not all(finite(t,nt,h,h,c,hbit,rng,40)for c in ctx[h]):continue
       cert=[]
       for s,rep,bs in((q,r,(0,1)),(r,r,(0,1)),(h,h,(hbit,))):
        for c in ctx[s]:
         for b in bs:
          ex=exact(t,nt,s,rep,c,b,40)
          if ex is None:break
          cert.append({'q':s,'ctx':c,'read':b,'cases':ex})
         else:continue
         break
        else:continue
        break
       else:
        print('FOUND',q,r,bit,(w,d,z),hb,action,flush=True);found.append({'q':q,'r':r,'row':[r,bit,w,d,z],'helper':[h,hbit,*action],'cert':cert});(p/'compat_fold_neutral_found.json').write_text(json.dumps(found,indent=2))
      nt[hb]=orig
 if i%20==0:print('progress',i,trials,repairs,len(found),time.time()-st,flush=True)
(p/'compat_fold_neutral_results.json').write_text(json.dumps({'trials':trials,'repairs':repairs,'found':len(found),'seconds':time.time()-st},indent=2));print('DONE',len(found),flush=True)
