from pathlib import Path
import sys,itertools,json,random,time
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent));import build221 as b
M=P;T=b.read_table((M/'q13_normal215.native.tm').read_bytes())
qs=sorted({q for q,k in T});random.seed(73191)
contexts=[]
for marker,q in[(0,91),(1,73)]:
 patterns=[0,(1<<15)-1]+[random.randrange(1<<15)for _ in range(20)]
 for bits in patterns:
  cells={i-7 for i in range(15)if bits>>i&1}
  cells.discard(0)
  if marker:cells.add(-1)
  else:cells.discard(-1);cells.add(-2)
  contexts.append((q,frozenset(cells)))
# Each old prefix is an admissible confluence target once at least one transition occurs.
def key(q,h,ones):return(q,h,frozenset(ones))
targets=[]
for q,ini in contexts:
 h=0;ones=set(ini);hist=set()
 for tick in range(100):
  if(q,int(h in ones))not in T:break
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
  if q not in(73,91):hist.add(key(q,h,ones))
 targets.append(hist)
survivors=[];counter=0;start=time.time()
for dest in qs:
 if dest==91:continue
 for w,d in itertools.product((0,1),(-1,1)):
  N={k:(ww,dd,73 if zz==91 else zz)for k,(ww,dd,zz)in T.items()if k[0]!=91};N[73,0]=(w,d,dest)
  lengths=[];good=True
  for(_,ini),hist in zip(contexts,targets):
   q=73;h=0;ones=set(ini);seen=set();ok=False
   for tick in range(100):
    z=key(q,h,ones)
    if tick and q not in(73,91)and z in hist:ok=True;lengths.append(tick);break
    if z in seen:break
    seen.add(z)
    if(q,int(h in ones))not in N:break
    ww,dd,q=N[q,int(h in ones)]
    if ww:ones.add(h)
    else:ones.discard(h)
    h+=dd
   if not ok:good=False;break
  counter+=1
  if good:
   print('SURVIVOR',w,d,dest,'maxsteps',max(lengths),flush=True);survivors.append({'newrow':[w,d,dest],'maxsteps':max(lengths)})
print('COMPLETE',counter,len(survivors),'seconds',time.time()-start,flush=True)
(P/'fold91_73_zero_prefix_sample.json').write_text(json.dumps({'status':'BOUNDED_SAMPLE_PREFIX_CONFLUENCE_SEARCH','table':str(M/'q13_normal215.native.tm'),'contexts':len(contexts),'variants':counter,'maxprefix':100,'survivors':survivors,'not_universal_proof':True},indent=2)+'\n')

