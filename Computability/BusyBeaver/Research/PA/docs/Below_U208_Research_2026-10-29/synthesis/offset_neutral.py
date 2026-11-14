from offset import *
QC={}
def quick_general(T,C,q,r,offset,oldstate,ctx,k,limit=40):
 if ctx.get(0,k)!=k:return True
 key=(tuple(sorted(ctx.items())),k)
 if key not in QC:
  vals={i:rng.randrange(2)for i in range(-50,51)};vals.update(ctx);vals[0]=k;QC[key]=vals
 vals=QC[key]
 w,d,z=T[oldstate,k];d+=offset if z==q else 0;z=r if z==q else z;expected=dict(vals);expected[0]=w
 s=r if oldstate==q else oldstate;h=offset if oldstate==q else 0;v=dict(vals)
 for _ in range(limit):
  if s==254 or h not in v:return False
  w1,d1,s=C[s,v[h]];v[h]=w1;h+=d1
  if(s,h)==(z,d)and v==expected:return True
 return False

def failing_rows(T,C,q,r,offset,ctx,k,limit=40):
 key=(tuple(sorted(ctx.items())),k)
 if key not in QC:
  vals={i:rng.randrange(2)for i in range(-50,51)};vals.update(ctx);vals[0]=k;QC[key]=vals
 vals=QC[key];w,d,z=T[q,k];d+=offset if z==q else 0;z=r if z==q else z
 expected=dict(vals);expected[0]=w;s=r;h=offset;v=dict(vals);rows=set()
 for _ in range(limit):
  if s==254 or h not in v:return rows
  rows.add((s,v[h]));w1,d1,s=C[s,v[h]];v[h]=w1;h+=d1
  if(s,h)==(z,d)and v==expected:return None
 return rows

def exact_general(T,C,q,r,offset,oldstate,ctx,b,limit=40):
 if ctx.get(0,b)!=b:return []
 ow,od,oz=T[oldstate,b];od+=offset if oz==q else 0;oz=r if oz==q else oz;ctx=dict(ctx);ctx[0]=b
 stack=[(r if oldstate==q else oldstate,offset if oldstate==q else 0,{},ctx,[])];cert=[]
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

def run(file,name):
 rec=json.load(open(file));T=read(Path(rec['input']));Q=sorted({q for q,k in T});ct,_=histories(T,12);inc={q:[]for q in Q}
 for(s,k),(w,d,z)in T.items():
  if z in inc:inc[z].append((s,k,w,d))
 changes=[tuple(a['row'])for a in rec['rewrites']];trials=0;pruned=0;finitepasses=0;found=[]
 for q in Q:
  if q==0:continue
  ds={d for s,k,w,d in inc[q]if s!=q}
  if len(ds)!=1:continue
  offset=-2*ds.pop()
  for r in Q:
   if r==q:continue
   C={(s,k):(w,d+offset if z==q else d,r if z==q else z)for(s,k),(w,d,z)in T.items()if s!=q}
   contexts=[(context,k)for k in(0,1)for context in ct[q]if context.get(0,k)==k]
   seen=None
   for context,k in contexts:
    seen=failing_rows(T,C,q,r,offset,context,k)
    if seen is not None:break
   for u,b,w,d,z in changes:
    if seen is not None and (u,b) not in seen:pruned+=1;continue
    if u==q:continue
    nd=d+offset if z==q else d
    if nd not in(-1,1):continue
    prior=C[u,b];C[u,b]=(w,nd,r if z==q else z);trials+=1
    if all(quick_general(T,C,q,r,offset,q,ctx,k)for ctx,k in contexts):
     finitepasses+=1
     if all(quick_general(T,C,q,r,offset,u,ctx,b)for ctx in ct[u]):
      cert=[]
      for oldstate,k,context in [(q,k,c)for c,k in contexts]+[(u,b,c)for c in ct[u]]:
       ex=exact_general(T,C,q,r,offset,oldstate,context,k)
       if ex is None:break
       cert.append({'oldstate':oldstate,'read':k,'context':context,'branches':ex})
      else:
       key=f'offset_neutral_{name}_{q}_{r}_{offset}_{u}_{b}_{w}_{d}_{z}';write(C,P/(key+'.tm'));(P/(key+'.json')).write_text(json.dumps(cert));found.append(key);print('FOUND',key,flush=True)
    C[u,b]=prior
  print(name,'q',q,'trials',trials,'finitepasses',finitepasses,'found',len(found),flush=True)
 result={'name':name,'neutral_receipt':str(file),'trials':trials,'pruned':pruned,'finitepasses':finitepasses,'found':found};(P/(name+'_offset_neutral_results.json')).write_text(json.dumps(result,indent=2));return result
if __name__=='__main__':
 run(P/'inputs/neutral.json','primary')
 run(P/'inputs/compat_neutral.json','compatibility')
