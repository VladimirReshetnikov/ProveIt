from pathlib import Path
import sys,itertools,json,random,time
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent));import build221 as b
M=P;T=b.read_table((M/'q13_normal215.native.tm').read_bytes());qs=sorted({q for q,k in T})
random.seed(1382)
def key(q,h,ones):return(q,h,frozenset(ones))
def contexts(bit):
 out=[]
 for line in (P/'contexts13_82.tsv').read_text().splitlines():
  q,b,ss=line.split();q=int(q);b=int(b)
  if b!=bit:continue
  old=frozenset(int(v)for v in ss.split(',')if v)
  new=set(old)
  if q==13:new.add(-1)
  out.append((q,old,frozenset(new),None))
 return out
def gethist(q,old):
 h=0;oq=q;ones=set(old);hist=set()
 for tick in range(1000):
  if(oq,int(h in ones))not in T:break
  w,d,oq=T[oq,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
  if oq not in(13,82):hist.add(key(oq,h,ones))
 return hist
ctx={b:contexts(b)for b in(0,1)}
def table(a0,a1):
 N={k:(ww,dd,82 if zz==13 else zz)for k,(ww,dd,zz)in T.items()if k[0]!=13}
 for k in((38,0),(42,0)):N[k]=(1,1,82)
 N[82,0]=a0;N[82,1]=a1;return N
def check(N,bit):
 lengths=[]
 for ix,(oldq,old,ini,hist) in enumerate(ctx[bit]):
  if hist is None:
   hist=gethist(oldq,old);ctx[bit][ix]=(oldq,old,ini,hist)
  q=82;h=0;ones=set(ini);seen=set()
  for tick in range(1000):
   z=key(q,h,ones)
   if tick and q not in(13,82)and z in hist:lengths.append(tick);break
   if z in seen:return None
   seen.add(z)
   if(q,int(h in ones))not in N:return None
   w,d,q=N[q,int(h in ones)]
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d
  else:return None
 return max(lengths)
zero=[];pairs=[];start=time.time()
for dest in qs:
 if dest==13:continue
 for w,d in itertools.product((0,1),(-1,1)):
  a=(w,d,dest);n=check(table(a,T[82,1]),0)
  if n is not None:zero.append(a);print('ZERO',a,n,flush=True)
print('ZEROCOUNT',len(zero),flush=True)
for a0 in zero:
 for dest in qs:
  if dest==13:continue
  for w,d in itertools.product((0,1),(-1,1)):
   a1=(w,d,dest);N=table(a0,a1);n=check(N,1)
   if n is not None and check(N,0)is not None:
    pairs.append([a0,a1]);file=P/f'marker13_82_{len(pairs)}.native.tm';file.write_bytes(b.table_bytes(N));print('PAIR',a0,a1,n,flush=True)
(P/'marker13_82_actual1000_search.json').write_text(json.dumps({'status':'FINITE_COLLECTED_CONTEXT_PREFIX_SAMPLE','contexts_per_bit':len(ctx[0]),'zero_survivors':zero,'pairs':pairs,'seconds':time.time()-start,'not_universal_proof':True},indent=2)+'\n')
print('COMPLETE',len(zero),len(pairs),'seconds',time.time()-start)

