from offset_neutral import *
def run(file,name):
 rec=json.load(open(file));T=read(Path(rec['input']));Q=sorted({q for q,k in T});ct,_=histories(T,12)
 I=abstract(T,4);ct[0]=[{i-4:(v>>i)&1 for i in range(9)}for v in sorted(I[0])]
 changes=[None]+[tuple(a['row'])for a in rec['rewrites']];q=0;offset=-2;trials=0;passes=0;found=[]
 assert all(d==1 for(s,k),(w,d,z)in T.items()if z==0 and s!=0)
 for r in Q:
  if r==q:continue
  C={(s,k):(w,d+offset if z==q else d,r if z==q else z)for(s,k),(w,d,z)in T.items()if s!=q}
  contexts=[(c,c[0])for c in ct[0]]
  seen=None
  for context,k in contexts:
   seen=failing_rows(T,C,q,r,offset,context,k)
   if seen is not None:break
  for change in changes:
   if change:
    u,b,w,d,z=change
    if u==q or(seen is not None and(u,b)not in seen):continue
    nd=d+offset if z==q else d
    if nd not in(-1,1):continue
    prior=C[u,b];C[u,b]=(w,nd,r if z==q else z)
   trials+=1
   if all(quick_general(T,C,q,r,offset,q,c,k)for c,k in contexts):
    passes+=1;cases=[(q,k,c)for c,k in contexts]+([(u,b,c)for c in ct[u]]if change else[])
    cert=[]
    for oldstate,k,c in cases:
     ex=exact_general(T,C,q,r,offset,oldstate,c,k)
     if ex is None:break
     cert.append({'oldstate':oldstate,'read':k,'context':c,'branches':ex})
    else:
     key=f'initial_offset_{name}_{r}_{change}';write(C,P/(key+'.tm'));(P/(key+'.json')).write_text(json.dumps({'start':r,'offset':offset,'change':change,'cases':cert}));found.append(key);print('FOUND',key,flush=True)
   if change:C[u,b]=prior
 result={'name':name,'q0_windows':len(ct[0]),'trials':trials,'finitepasses':passes,'found':found};print(result,flush=True);return result
if __name__=='__main__':
 r=[run(P/'inputs/neutral.json','primary'),run(P/'inputs/compat_neutral.json','compatibility')];(P/'initial_offset_results.json').write_text(json.dumps(r,indent=2))
