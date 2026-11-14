from pathlib import Path
import itertools,json
ls=(Path(__file__).resolve().parent/'fixed_rows.txt').read_text().splitlines();rows={}
for s in ls[1:]:
 q,w,d,n,v,e,m=map(int,s.split());rows[q,0]=(w,d,n);rows[q,1]=(v,e,m)
qs=sorted({q for q,b in rows})
def sim(action,ctx,neighbor,k):
 h,wr,direction=action;q,pos=h,1 if direction else -1
 orig=[0]*(2*k+1);other=[p for p in range(-k,k+1)if p not in(-1,0)]
 for p,b in zip(other,neighbor):orig[p+k]=b
 orig[k-1]=ctx;tape=list(orig);tape[k]=wr;target=105 if ctx==0 else 104;seen=set()
 for n in range(150):
  if q==target and pos==1 and tape==orig:return n
  if not-k<=pos<=k or(q,tape[pos+k])not in rows or(q,pos,*tape)in seen:return
  seen.add((q,pos,*tape));w,d,q=rows[q,tape[pos+k]];tape[pos+k]=w;pos+=1 if d else -1
allhits=[]
for k in range(1,5):
 hits=[];neighbor=list(itertools.product((0,1),repeat=2*k-1))
 for action in itertools.product(qs,(0,1),(0,1)):
  durations=[]
  for ctx,nb in itertools.product((0,1),neighbor):
   n=sim(action,ctx,nb,k)
   if n is None:break
   durations.append(n)
  else:hits.append([action,max(durations)])
 allhits.append(dict(radius=k,neighbor_patterns=len(neighbor),hits=hits));print(allhits[-1],flush=True)
(Path(__file__).resolve().parent/'swapped_window_helpers.json').write_text(json.dumps(allhits,indent=2)+'\n')
