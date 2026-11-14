from conditional_pair import *
import random
rng=random.Random(20261029)
def quick(T,C,q,r,offset,ctx,k,limit=40):
 if ctx.get(0,k)!=k:return True
 vals={i:rng.randrange(2)for i in range(-50,51)};vals.update(ctx);vals[0]=k
 w,d,z=T[q,k];d+=offset if z==q else 0;z=r if z==q else z;expected=dict(vals);expected[0]=w
 s=r;h=offset;v=dict(vals)
 for _ in range(limit):
  if s==254 or h not in v:return False
  w1,d1,s=C[s,v[h]];v[h]=w1;h+=d1
  if(s,h)==(z,d)and v==expected:return True
 return False

def exact_offset(T,C,q,r,offset,ctx,b,limit=40):
 if ctx.get(0,b)!=b:return []
 ow,od,oz=T[q,b];od+=offset if oz==q else 0;oz=r if oz==q else oz;ctx=dict(ctx);ctx[0]=b
 stack=[(r,offset,{},ctx,[])];cert=[]
 while stack:
  s,h,writes,vals,tr=stack.pop()
  if tr and(s,h)==(oz,od)and all(writes.get(x,vals.get(x,('v',x)))==(ow if x==0 else vals.get(x,('v',x)))for x in set(writes)|{0}):cert.append({'input':vals,'trace':tr});continue
  if s==254 or len(tr)>=limit:return None
  k=writes.get(h,vals.get(h))
  if k is None:
   for bit in(0,1):v=dict(vals);v[h]=bit;stack.append((s,h,dict(writes),v,tr))
   continue
  w,d,z=C[s,k];wr=dict(writes);wr[h]=w;stack.append((z,h+d,wr,vals,tr+[[s,h,k,w,d,z]]))
  if len(stack)+len(cert)>4096:return None
 return cert

def run(name,file,depth=8):
 T=read(file);Q=sorted({q for q,k in T});ct,cnt=histories(T,depth);inc={q:[]for q in Q}
 for(s,k),(w,d,z)in T.items():
  if z in inc:inc[z].append((s,k,w,d))
 eligible=[];trials=0;exacttrials=0;found=[]
 for q in Q:
  if q==0:continue
  # No incoming self edge: deleted state's own transition requires separate offset simulation.
  directions={d for s,k,w,d in inc[q]if s!=q}
  if len(directions)!=1:continue
  offset=-2*next(iter(directions));eligible.append([q,offset])
  for r in Q:
   if q==r:continue
   trials+=1;C={(s,k):(w,d+offset if z==q else d,r if z==q else z)for(s,k),(w,d,z)in T.items()if s!=q}
   assert all(d in(-1,1)for w,d,z in C.values())
   if not all(quick(T,C,q,r,offset,context,k)for k in(0,1)for context in ct[q]):continue
   exacttrials+=1;cert=[]
   for k in(0,1):
    for context in ct[q]:
     ex=exact_offset(T,C,q,r,offset,context,k)
     if ex is None:break
     cert.append({'read':k,'context':context,'branches':ex})
    else:continue
    break
   else:
    key=f'offset_{name}_{q}_{r}_{offset}';write(C,P/(key+'.tm'));(P/(key+'.json')).write_text(json.dumps({'remove':q,'representative':r,'offset':offset,'depth':depth,'cases':cert}));found.append(key);print('FOUND',key,flush=True)
 result={'name':name,'depth':depth,'eligible':eligible,'trials':trials,'exact_trials':exacttrials,'found':found};print(name,len(eligible),trials,exacttrials,found,flush=True);return result
if __name__=='__main__':
 r=[run('primary',ROOT/'machine/u208.native.tm'),run('compatibility',ROOT/'alternative/u208.native.tm')];(P/'offset_results.json').write_text(json.dumps(r,indent=2))
