from pathlib import Path
import sys,itertools,time,json,collections
sys.path.insert(0,str(Path(__file__).resolve().parent));import check_joint_fold as c,filter_source as f
from settings import Z,OUT
T,start=c.read(Z/'candidate-k218/k218.native.tm');Q=sorted({q for q,b in T});I=c.domain(T,start,7);r=7;F=97;cache={};count=0;hits=[];out=OUT;out.mkdir(exist_ok=True);started=time.monotonic()
incoming=collections.defaultdict(list)
for k,v in T.items():incoming[v[2]].append((k,v))

def filt(N,keep,drop,tag,complete=False):
 phi=lambda q:keep if q==drop else q
 for q in (sorted(Q)if complete else(drop,keep)):
  for bit in(0,1):
   w,d,z=T[q,bit]
   if q!=drop and N[q,bit]==(w^(z==drop),d,phi(z))and(z!=drop or tag==-d):continue
   key=('ws',q,bit)
   if key not in cache:
    ws=sorted(m for m in I[q]if(m>>r)&1==bit);cache[key]=[ws[0],ws[-1],*ws[1:-1]]if len(ws)>2 else ws
   for m in cache[key]:
    key=(q,m)
    if key not in cache:
     oq,oh,om=q,0,m;path=[];oldhalt=False
     for tick in range(F):
      if oq==254 or not-r<=oh<=r:break
      b=(om>>(oh+r))&1;ow,od,oq=T[oq,b];om=(om&~(1<<(oh+r)))|(ow<<(oh+r));oh+=od;path.append((oq,oh,om));oldhalt|=oq==254
     cache[key]=path,oldhalt
    path,oldhalt=cache[key];goals=set()
    for oq,oh,om in path:
     if oq==drop:
      if not-r<=oh+tag<=r:continue
      om^=1<<(oh+tag+r)
     goals.add((phi(oq),oh,om))
    nq,nh,nm=phi(q),0,m^((1<<(tag+r))if q==drop else 0);seen=set();joined=False;why='fuel'
    for tick in range(F):
     if nq==254 or not-r<=nh<=r:why='window';break
     if(nq,nh,nm)in seen:why='cycle';break
     seen.add((nq,nh,nm));b=(nm>>(nh+r))&1;w,d,nq=N[nq,b];nm=(nm&~(1<<(nh+r)))|(w<<(nh+r));nh+=d
     if nq==254:joined=oldhalt;why='halt';break
     if(nq,nh,nm)in goals:joined=True;break
    if not joined:return (q,bit,m,why)
 return None

pairs=[]
for keep,drop in itertools.permutations(Q,2):
 if drop==start:continue
 dirs={v[1]for(k,b),v in incoming[drop]if k not in(keep,drop)}
 if len(dirs)!=1:continue
 direction=next(iter(dirs));tag=-direction
 phi=lambda z:keep if z==drop else z
 N={(q,b):(w^(z==drop),d,phi(z))for(q,b),(w,d,z)in T.items()if q!=drop}
 acts=[sorted({(w,d,phi(z))for q in(keep,drop)for w,d,z in[T[q,b]]}|{(w^1,d,keep)for q in(keep,drop)for w,d,z in[T[q,b]]if z==drop})for b in(0,1)]
 common=[b for b in(0,1)if len(acts[b])==1]
 variants=list(itertools.product(*acts))
 if len(common)==1:
  fixed=common[0];other=1-fixed
  for action in itertools.product((0,1),(-1,1),[q for q in Q if q!=drop]+[254]):
   if action in acts[other]:continue
   aa=[None,None];aa[fixed]=acts[fixed][0];aa[other]=action;variants.append(tuple(aa))
 for a0,a1 in variants:
  count+=1;N[keep,0]=a0;N[keep,1]=a1;bad=filt(N,keep,drop,tag)
  if bad is not None:continue
  print('SURVIVOR',keep,drop,tag,a0,a1,flush=True)
  bad=filt(N,keep,drop,tag,True)
  if bad is not None:print('FULL_REJECT',bad,flush=True);continue
  i=len(hits);h={'keep':keep,'drop':drop,'tag':tag,'actions':[a0,a1]};hits.append(h);(out/f'hit{i:03d}.native.tm').write_bytes(f.encode(N,start));(out/f'hit{i:03d}.json').write_text(json.dumps(h,indent=2));print('HIT',h,flush=True)
 pairs.append((keep,drop,tag))
 if len(pairs)%3000==0:print('PROGRESS',len(pairs),count,len(hits),round(time.monotonic()-started,2),flush=True)
 if time.monotonic()-started>240:break
(out/'result.json').write_text(json.dumps({'attempted':count,'pairs':len(pairs),'hits':hits,'seconds':time.monotonic()-started},indent=2));print('DONE',count,len(hits),flush=True)
