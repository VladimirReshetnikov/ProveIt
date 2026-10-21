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
     seen.add((nq,nh,nm));b=(nm>>(nh+r))&1
     if N[nq,b] is None:return ('need',b)
     w,d,nq=N[nq,b];nm=(nm&~(1<<(nh+r)))|(w<<(nh+r));nh+=d
     if nq==254:joined=oldhalt;why='halt';break
     if(nq,nh,nm)in goals:joined=True;break
    if not joined:return (q,bit,m,why)
 return None

pairs=[]
for keep,drop in itertools.permutations(Q,2):
 if 0 in(keep,drop):continue
 if not any(T[keep,b]==T[drop,b]for b in(0,1)):continue
 if len({v[:2]for k,v in incoming[keep]+incoming[drop]})!=1:continue
 if incoming[keep][0][1][1]!=1:continue
 pairs.append((keep,drop))
attempted=0;covered=0
for keep,drop in pairs:
 phi=lambda z:keep if z==drop else z
 N={(q,b):(w^(z==drop),d,phi(z))for(q,b),(w,d,z)in T.items()if q!=drop};N[keep,0]=N[keep,1]=None
 targets=[q for q in Q if q!=drop]+[254]
 def walk():
  global attempted,covered
  attempted+=1;bad=filt(N,keep,drop,-1)
  depth=sum(N[keep,b]is not None for b in(0,1))
  if bad is not None and bad[0]!='need':covered+=len(targets)**(2-depth);return
  if bad is None:
   pending=next((b for b in(0,1)if N[keep,b]is None),None)
   if pending is None:
    assert filt(N,keep,drop,-1,True)is None
    i=len(hits);h={'keep':keep,'drop':drop,'tag':-1,'actions':[N[keep,0],N[keep,1]]};hits.append(h);(out/f'hit{i:03d}.native.tm').write_bytes(f.encode(N,start));(out/f'hit{i:03d}.json').write_text(json.dumps(h,indent=2));print('HIT',h,flush=True);return
  else:pending=bad[1]
  for target in targets:
   N[keep,pending]=(pending,-1,target);walk()
  N[keep,pending]=None
 walk();print('PAIR',keep,drop,'partial',attempted,'covered',covered,'hits',len(hits),'seconds',round(time.monotonic()-started,2),flush=True)
 if time.monotonic()-started>180:break
(out/'result.json').write_text(json.dumps({'partial_checks':attempted,'covered':covered,'pairs':len(pairs),'hits':hits,'seconds':time.monotonic()-started},indent=2));print('DONE',attempted,covered,len(hits),flush=True)
