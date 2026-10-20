from fold_search import *
import contextlib,io,hashlib

def one(t):
 states=sorted({q for q,b in t});facts=invariants(t);permitted={};actions=[(w,d,z) for w in (0,1) for d in (-1,1) for z in states if z!=0]
 for q in states:
  if q==0:continue
  for b in (0,1):
   if facts[q].get(0,b)!=b:permitted[q,b]=None;continue
   initial=facts[q]|{0:b};w,d,z=t[q,b];expected=initial|{0:w}
   permitted[q,b]={act for act in actions if block(t,q,initial,(z,d,expected),act,banned=(q,))}
 for p,q in itertools.combinations([q for q in states if q!=0],2):
  ps=[]
  for b in (0,1):
   a,c=permitted[p,b],permitted[q,b];v=(a&c if a is not None and c is not None else a if a is not None else c)
   if v is None:v={t[p,b]}
   if not v:break
   ps.append(v)
  if len(ps)!=2:continue
  for a0,a1 in itertools.product(*ps):
   phi=lambda s:p if s==q else s
   new={(s,b):(w,d,phi(z)) for (s,b),(w,d,z) in t.items() if s!=q}
   new[p,0]=(a0[0],a0[1],phi(a0[2]));new[p,1]=(a1[0],a1[1],phi(a1[2]))
   good=True
   for s,b in itertools.product((p,q),(0,1)):
    if facts[s].get(0,b)!=b:continue
    initial=facts[s]|{0:b};w,d,z=t[s,b];expected=initial|{0:w}
    if not block(new,p,initial,(phi(z),d,expected)):good=False;break
   if good:yield new,{'keep':p,'delete':q,'a0':a0,'a1':a1,'invariant':{s:fs for s,fs in facts.items() if fs}}

if __name__=='__main__':
 t=read_table(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
 queue=[(t,[])];seen={hashlib.sha256(encode(t).encode()).hexdigest()};start=time.time();best=len(t)//2
 for index,(t,path) in enumerate(queue):
  n=len(t)//2
  if n<best:best=n;print('BEST',best,'searched',index,'queue',len(queue),'seconds',time.time()-start,flush=True)
  for new,spec in one(t):
   digest=hashlib.sha256(encode(new).encode()).hexdigest()
   if digest in seen:continue
   seen.add(digest);newpath=path+[spec];queue.append((new,newpath))
   (out/f'{len(new)//2}-{digest[:16]}.tm').write_text(encode(new));(out/f'{len(new)//2}-{digest[:16]}.json').write_text(json.dumps(newpath,indent=2)+'\n')
  if index%25==0:print('progress',index,'queue',len(queue),'best',best,'sec',time.time()-start,flush=True)
 print('DONE',len(queue),'best',best,'sec',time.time()-start)
