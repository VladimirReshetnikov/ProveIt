"""Exact finite ray/cycle certificates for every blank starting control.

This concerns only the explicitly supplied append-zero mutation; it is not
a state lower bound or a theorem about another program layout.
"""
from pathlib import Path
import hashlib,json,sys
p=Path(sys.argv[1]);rows={}
for ln in p.read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
results=[]
for start in sorted({q for q,b in rows}):
 q,h,ones=start,0,set();seen={};trace=[]
 for k in range(100000):
  key=(q,tuple(sorted(i-h for i in ones)))
  if key in seen:
   first,oldh=seen[key]
   result={'start':start,'kind':'translated_cycle','steps':k,'first_step':first,'period':k-first,'shift':h-oldh};break
  seen[key]=(k,h)
  b=int(h in ones)
  if (q,b) not in rows:
   result={'start':start,'kind':'halt','steps':k,'state':q};break
  w,d,n=rows[q,b]
  if b==0 and n==q and all((i-h)*d<0 for i in ones):
   result={'start':start,'kind':'blank_ray','steps':k,'state':q,'head':h,'direction':d,'write':w,'one_cells':sorted(ones)};break
  trace.append([q,h,b,w,d,n])
  (ones.add if w else ones.discard)(h);h+=d;q=n
 else:
  result={'start':start,'kind':'unresolved','steps':100000}
 result['trace_sha256']=hashlib.sha256(json.dumps(trace,separators=(',',':')).encode()).hexdigest()
 results.append(result)
out={'table':p.name,'table_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'working_states':len(results),'results':results,'counts':{kind:sum(z['kind']==kind for z in results)for kind in sorted({z['kind']for z in results})}}
print(json.dumps(out,indent=2))
