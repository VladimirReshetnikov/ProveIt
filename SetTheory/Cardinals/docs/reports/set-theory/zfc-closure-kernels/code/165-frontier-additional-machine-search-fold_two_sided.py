from pathlib import Path
import json,itertools,time
BASE=Path(__file__).resolve().parent;K=BASE.parent/'baseline/k215'
T={}
for l in(K/'k215.native.tm').read_text().splitlines():
 if not l or l.startswith('#'):continue
 q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
states=sorted({q for q,b in T});rewrites=[None]
for l in(BASE/'local_rewrites7.txt').read_text().splitlines():
 q,b,w,d,z,n,*_=l.split();rewrites.append(((int(q),int(b)),(int(w),int(d),int(z))))
def search(O):
 inc={q:[]for q in states}
 for k,(w,d,z)in O.items():
  if z in inc:inc[z].append((*k,w,d))
 results=[];candidates=[]
 for a,b in itertools.combinations(states,2):
  if not a:continue
  ia,ib=inc[a],inc[b]
  if not ia or not ib or not all(z[3]==ia[0][3]and z[2]==ia[0][2]for z in ia)or not all(z[3]==ib[0][3]and z[2]==ib[0][2]for z in ib)or ia[0][2]==ib[0][2]or ia[0][3]!=ib[0][3]:continue
  for x in(0,1):
   if O[a,1-x]!=O[b,1-x]or O[a,x]==O[b,x]:continue
   candidates.append((a,b,x,ia[0][2],ib[0][2],ia[0][3]))
 for a,b,x,ma,mb,din in candidates:
  markerpos=-din;N={k:(w,d,a if z==b else z)for k,(w,d,z)in O.items()if k[0]!=b}
  for p in states:
   if p==b:continue
   for initw in(0,1):
    N[a,x]=(initw,markerpos,p);traces=[]
    for state,marker in((a,ma),(b,mb)):
     w,d,z=O[state,x];z=a if z==b else z;t={markerpos:marker,0:initw};q=p;h=markerpos;seen=set();path=[];ok=False
     for tick in range(40):
      if(q,h,t)==(z,d,{markerpos:marker,0:w}):ok=True;break
      if h not in t or(q,t[h])not in N:break
      key=(q,h,t[markerpos],t[0])
      if key in seen:break
      seen.add(key);act=N[q,t[h]];path.append((q,h,t[h],*act));t[h],dd,q=act;h+=dd
     if not ok:break
     traces.append(path)
    if len(traces)==2:results.append(dict(a=a,b=b,x=x,p=p,initw=initw,dir=markerpos,markers=[ma,mb],traces=traces))
 return results
out=[]
for i,r in enumerate(rewrites):
 N=dict(T)
 if r:key,alt=r;N[key]=alt
 folds=search(N)
 if folds:
  rec=dict(rewrite=r,folds=folds);out.append(rec);print(json.dumps(rec),flush=True)
print('TESTED',len(rewrites),'FOUND',len(out));(BASE/'replay_two_sided_fold_results.json').write_text(json.dumps(out,indent=2))
