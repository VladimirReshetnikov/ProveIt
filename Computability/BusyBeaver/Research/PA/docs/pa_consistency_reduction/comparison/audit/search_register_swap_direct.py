#!/usr/bin/env python3
from pathlib import Path
import sys,time,json,itertools,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();base=S.load_machine();logical=list(S.PHYSICAL);entry={r:q for q,r in S.SKIPS.items()};states=sorted({q for q,b in base});protected={q for q,b in S.ENGINE_ROWS}|{base[k][2]for k in S.ENGINE_ROWS}|{0,S.ROOT};results=[];hits=[]
class Fold:
 def __init__(self,m,q,r):self.m,self.q,self.r=m,q,r
 def get(self,k,default=None):
  q,b=k
  if q==self.q:q=self.r
  v=self.m.get((q,b),default)
  if v is None:return None
  w,d,z=v
  return(w,d,self.r if z==self.q else z)
for a,b in itertools.combinations([r for r in range(9)if r!=6],2):
 perm=list(range(9));perm[a],perm[b]=b,a;S.PHYSICAL=[perm[r]for r in logical]
 m={k:(w,d,entry[perm[S.SKIPS[z]]])if k not in S.ENGINE_ROWS and z in S.SKIPS else(w,d,z)for k,(w,d,z)in base.items()}
 cs=S.contracts();first=collections.defaultdict(list);bad=None
 for i,branch,br,s,t in cs:
  trace=[]
  if S.execute(m,br,s,t,record=trace)is None:bad=(i,branch);break
  seen=set()
  for tag,v,row in trace:
   q=v[0]
   if tag=='step'and q not in seen:first[q].append((br,v,t,i,branch));seen.add(q)
 record={'swap':[a,b],'baseline_failed':bad,'trials':0}
 if bad is not None:results.append(record);print('INVALID',a,b,bad,flush=True);continue
 for q in states:
  if q in protected:continue
  for r in states:
   if r==q:continue
   fm=Fold(m,q,r);record['trials']+=1
   if any(S.execute(fm,br,(r,)+v[1:],t)is None for br,v,t,i,branch in first[q]):continue
   nm={k:(w,d,r if z==q else z)for k,(w,d,z)in m.items()if k[0]!=q}
   try:summary,_=S.verify(nm)
   except AssertionError:continue
   hit={'swap':[a,b],'drop':q,'keep':r,'summary':summary,'PHYSICAL':S.PHYSICAL};hits.append(hit);stem=f'register_swap_{a}_{b}_fold_{q}_{r}';hit['stem']=stem
   (out/(stem+'.tm')).write_text(''.join(f'{u} {bb} {w} {"R"if d==1 else"L"} {z}\n'for(u,bb),(w,d,z)in sorted(nm.items())))
   (out/(stem+'_sites.json')).write_text(json.dumps(S.all_sites())+'\n');print('HIT',hit,flush=True)
 results.append(record);print('DONE',a,b,record['trials'],'elapsed',round(time.monotonic()-start,1),flush=True)
 (out/'register_swap_direct_results.json').write_text(json.dumps({'records':results,'hits':hits,'seconds':time.monotonic()-start},indent=2)+'\n')
print('ALL DONE',len(results),'hits',len(hits),'seconds',time.monotonic()-start,flush=True)
