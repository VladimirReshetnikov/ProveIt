"""Own finite literal decoder-role census. No supplied code or runtime invoked."""
from pathlib import Path
import json,hashlib,collections,itertools
A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20')
O=Path(__file__).parent
T={}
for line in (A/'binary/machine/k218.native.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(z))
rows=json.loads((A/'source/sites218.json').read_text());leaves={p:(o,r)for p,o,r in rows};nodes={}
def tree(p=''):
 if p in leaves:t=leaves[p]
 else:t=(tree(p+'0'),tree(p+'1'))
 nodes[p]=t;return t
root=tree();roles=collections.defaultdict(list);errors=[];traces={}
for p,n in nodes.items():
 if isinstance(n[0],str):continue
 ones={-1}|{i for i,b in enumerate(p)if b=='1'};initial=set(ones);q,h=84,0;trace=[]
 for tick in range(256):
  if h==len(p):break
  if h>len(p)or(q,int(h in ones))not in T:break
  b=int(h in ones);w,d,z=T[q,b];trace.append([q,h,b,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q,h=z,h+d
 if h!=len(p)or ones!=initial:errors.append(dict(prefix=p,q=q,head=h,steps=len(trace),restored=ones==initial))
 else:roles[q].append(p);traces[p]=trace
assert not errors,errors[:3]
nodeid=lambda t:hashlib.sha256(json.dumps(t,separators=(',',':')).encode()).hexdigest()
by={q:dict(prefixes=ps,types=sorted({nodeid(nodes[p])for p in ps}),rows=[T[q,b]for b in (0,1)],incoming=[[s,b,*a[:2]]for(s,b),a in T.items()if a[2]==q])for q,ps in roles.items()}
pairs=[]
for q,r in itertools.combinations(sorted(roles),2):
 same=[b for b in(0,1)if T[q,b]==T[r,b]]
 if same:pairs.append(dict(pair=[q,r],same=same,rows=[[T[x,b]for b in(0,1)]for x in(q,r)],suffixes=[sorted({p[-1:]for p in roles[x]})for x in(q,r)],prefix_counts=[len(roles[x])for x in(q,r)]))
# Exact full-row equality is an immediate graph quotient, if any.
identical=[x for x in pairs if len(x['same'])==2]
reached={0};todo=[0]
while todo:
 q=todo.pop()
 for b in(0,1):
  z=T[q,b][2]
  if z!=254 and z not in reached:reached.add(z);todo.append(z)
assert reached=={q for q,b in T}
out=dict(status='OWN_DECODER_PREFIX_CENSUS_PASS',table_sha256=hashlib.sha256((A/'binary/machine/k218.native.tm').read_bytes()).hexdigest(),source_sha256=hashlib.sha256((A/'source/sites218.json').read_bytes()).hexdigest(),scope='Finite literal decoding to first arrival at every internal prefix; checks whole known-prefix tape restored. Not full primitive/startup or arbitrary-window fold acceptance.',internal_occurrences=len(nodes)-len(leaves),physical_decoder_states=len(roles),all_working_states=len(reached),roles=by,one_equal_branch_pairs=pairs,identical_row_pairs=identical)
(O/'roles.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in('roles','one_equal_branch_pairs')},indent=2))
print('selected',json.dumps({q:by.get(q)for q in(69,85,96,115,188,212,224,400)},indent=2))
print('pairs',json.dumps(pairs,indent=2))
