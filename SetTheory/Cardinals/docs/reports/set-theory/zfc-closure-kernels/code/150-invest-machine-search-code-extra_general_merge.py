from pathlib import Path
import json,sys,itertools,time,collections
sys.path.insert(0,str(Path(__file__).resolve().parent));import check_joint_fold as c,filter_source as f
from settings import Z,OUT
T,start=c.read(Z/'candidate-k218/k218.native.tm');Q=sorted({q for q,b in T});A={k:set()for k in T}
for h in json.loads((Path(__file__).resolve().parents[1]/'data/single_public_result.json').read_text())['hits']:A[h['q'],h['bit']].add(tuple(h['new']))
I=c.domain(T,start,7);cache={};count=0;seeds=0;hits=[];out=OUT;out.mkdir(exist_ok=True);started=time.monotonic()
incoming=collections.defaultdict(list)
for k,v in T.items():incoming[v[2]].append((k,v))
marker={q:{v[0]for k,v in incoming[q]if v[1]==1}for q in Q}
pairs=[]
for fixed in(0,1):
 for q,r in itertools.combinations(Q,2):
  if T[q,fixed]!=T[r,fixed] or T[q,1-fixed]==T[r,1-fixed]:continue
  pairs.extend([(fixed,q,r),(fixed,r,q)])
def filter_extra(N,q,r,extra):
 phi=lambda z:q if z==r else z
 keep,read=extra
 for b in(0,1):
  w,d,z=T[keep,b]
  if N[keep,b]==(w,d,phi(z)):continue
  for m in I[keep]:
   if (m>>7)&1!=b:continue
   oq,oh,om=keep,0,m;goals=set();oldhalt=False
   for _ in range(97):
    if oq==254 or not -7<=oh<=7:break
    bit=(om>>(oh+7))&1;w,d,oq=T[oq,bit];om=(om&~(1<<(oh+7)))|(w<<(oh+7));oh+=d;goals.add((phi(oq),oh,om));oldhalt|=oq==254
   nq,nh,nm=keep,0,m;okay=False;seen=set()
   for _ in range(97):
    if nq==254 or not -7<=nh<=7 or (nq,nh,nm)in seen:break
    seen.add((nq,nh,nm));bit=(nm>>(nh+7))&1;w,d,nq=N[nq,bit];nm=(nm&~(1<<(nh+7)))|(w<<(nh+7));nh+=d
    if nq==254:okay=oldhalt;break
    if(nq,nh,nm)in goals:okay=True;break
   if not okay:return False
 return True
for fixed,q,r in pairs:
 phi=lambda z:q if z==r else z
 act=lambda v:(v[0],v[1],phi(v[2]))
 N={(s,b):act(v)for(s,b),v in T.items()if s!=r};N[q,fixed]=act(T[q,fixed]);other=1-fixed
 for a in itertools.product((0,1),(-1,1),[s for s in Q if s!=r]+[254]):
  N[q,other]=a;seeds+=1;bad=f.local_filter(T,N,I,q,r,cache,97,7)
  if bad is None:continue
  oq=bad['old_row'][0];m=bad['window'];nq,nh,nm=q,0,m;seen=set();keys=set()
  for _ in range(97):
   if nq==254 or not -7<=nh<=7 or(nq,nh,nm)in seen:break
   seen.add((nq,nh,nm));b=(nm>>(nh+7))&1;key=(nq,b)
   if nq not in(q,r)and A.get(key):keys.add(key)
   w,d,nq=N[key];nm=(nm&~(1<<(nh+7)))|(w<<(nh+7));nh+=d
  for key in keys:
   old=N[key]
   for v in A[key]:
    av=act(v)
    if av==old:continue
    count+=1;N[key]=av
    fail=f.local_filter(T,N,I,q,r,cache,97,7)
    if fail is not None:continue
    if not filter_extra(N,q,r,key):continue
    h={'keep':q,'drop':r,'merged':[N[q,0],N[q,1]],'extra':key,'action':av};print('HIT',h,flush=True)
    proof=c.check(T,N,start,phi(start),q,r,7,97);i=len(hits);hits.append(h);(out/f'hit{i:03d}.tm').write_bytes(f.encode(N,phi(start)));(out/f'proof{i:03d}.json').write_text(json.dumps(proof,indent=2));print('PROVED',i,flush=True)
   N[key]=old
  if time.monotonic()-started>240:raise RuntimeError('time limit')
 print('PAIR',fixed,q,r,'attempts',count,'seed',seeds,'hits',len(hits),'seconds',round(time.monotonic()-started,2),flush=True)
(out/'result.json').write_text(json.dumps({'attempted':count,'seed_candidates':seeds,'hits':hits,'pairs':pairs,'seconds':time.monotonic()-started},indent=2));print('DONE',count,len(hits))
