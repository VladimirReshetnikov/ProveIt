from pathlib import Path
import json,itertools
BASE=Path(__file__).resolve().parent;K=BASE.parent/'baseline/k215'
T={}
for l in (K/'k215.native.tm').read_text().splitlines():
 if not l or l.startswith('#'):continue
 q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
states=sorted({q for q,b in T})
rewrites=[]
for l in (BASE/'local_rewrites7.txt').read_text().splitlines():
 q,b,w,d,z,n,*_=l.split();rewrites.append(((int(q),int(b)),(int(w),int(d),int(z))))
def search(N):
 inc={q:[] for q in states}
 for k,(w,d,z)in N.items():
  if z in inc:inc[z].append((*k,w,d))
 candidates=[]
 for a,b in itertools.combinations(states,2):
  if not a:continue
  ia,ib=inc[a],inc[b]
  if not ia or not ib or not all(z[3]==1 and z[2]==ia[0][2]for z in ia)or not all(z[3]==1 and z[2]==ib[0][2]for z in ib)or ia[0][2]==ib[0][2]:continue
  for x in(0,1):
   if N[a,1-x]!=N[b,1-x]or N[a,x]==N[b,x]:continue
   candidates.append((a,b,x,ia[0][2],ib[0][2]))
 results=[]
 for a,b,x,ma,mb in candidates:
  for p in states:
   if p in(a,b):continue
   for initw in(0,1):
    traces=[]
    for state,marker in((a,ma),(b,mb)):
     w,d,z=N[state,x];t={-1:marker,0:initw};q=p;h=-1;seen=set();path=[];ok=False
     for tick in range(30):
      if(q,h,t)==(z,d,{-1:marker,0:w}):ok=True;break
      if h not in t or q in(a,b)or(q,t[h])not in N:break
      key=(q,h,t[-1],t[0])
      if key in seen:break
      seen.add(key);act=N[q,t[h]];path.append((q,h,t[h],*act));t[h],dd,q=act;h+=dd
     if not ok:break
     traces.append(path)
    if len(traces)==2:results.append(dict(a=a,b=b,x=x,p=p,initw=initw,markers=[ma,mb],traces=traces))
 return results
out=[]
for i,(key,alt)in enumerate(rewrites):
 N=dict(T);N[key]=alt
 folds=search(N)
 if folds:
  rec=dict(rewrite=[*key,*alt],folds=folds);out.append(rec);print(json.dumps(rec),flush=True)
print('TESTED',len(rewrites),'FOUND',len(out));(BASE/'replay_rewrites_fold_results.json').write_text(json.dumps(out,indent=2))
