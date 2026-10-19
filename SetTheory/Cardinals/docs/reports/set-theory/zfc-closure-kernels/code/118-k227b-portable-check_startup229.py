from pathlib import Path
from collections import Counter
import hashlib,json,runpy
H=Path(__file__).resolve().parent;D=H/'delayed_erasure229'
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)

def require(x,m):
 if not x:raise ValueError(m)
def table(p):
 T={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,z=l.split();T[int(q),int(b)]=int(w),1 if d=='R'else-1,int(z)
 return T
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
O=table(H/'upstream/K230/machine/k230.tm');N=table(D/'candidate.klabels.tm');phi=lambda q:71 if q==140 else q
q=qn=0;h=hn=0;ones=set();newones=set();vis=Counter();clock=0;ng=0
def step(T,q,h,S):
 w,d,z=T[q,int(h in S)]
 if w:S.add(h)
 else:S.discard(h)
 return z,h+d
spec={(71,0):5,(140,0):3,(140,1):5,(80,1):9}
for tick in range(408419):
 require((phi(q),h,ones)==(qn,hn,newones),('before',tick))
 key=q,int(h in ones);vis[key]+=1
 if key==(140,1):require(h+1 in ones,('right guard',tick));ng+=1
 q,h=step(O,q,h,ones);dt=spec.get(key,1)
 for _ in range(dt):qn,hn=step(N,qn,hn,newones)
 clock+=dt;require((phi(q),h,ones)==(qn,hn,newones),('after',tick))
require((q,h,len(ones))==(84,-5,351),('endpoint',q,h,len(ones)))
C=table(D/'candidate.canonical.tm');M={int(q):z for q,z in json.loads((D/'renumbering.json').read_text())['k_to_canonical'].items()};off=clock+1;mem=bytearray(2*clock+3);pos=off;st=0
for tick in range(clock):
 w,d,z=C[st,mem[pos]];mem[pos]=w;pos+=d;st=z
found={i-off for i,b in enumerate(mem)if b};require((st,pos-off,found)==(M[qn],hn,newones),'dense canonical mismatch')
head=hn;header=min(v for v in newones if v>=head);vals=[];p=header+1
while p<=max(newones):
 require(p not in newones and p+1 in newones,'bad register');p+=1;first=p
 while p in newones:p+=1
 vals.append(p-first-1)
require(vals[:9]==[0,0,0,3,0,0,3,0,0] and vals[9:]==[1]*167,'seed')
res={'status':'PASS_EXACT_BLANK_PREFIX_AND_INDEPENDENT_DENSE_CANONICAL_RUN','input_sha256':sha(H/'upstream/K230/machine/k230.tm'),'klabels_sha256':sha(D/'candidate.klabels.tm'),'canonical_sha256':sha(D/'candidate.canonical.tm'),'engine_table_sha256':sha(D/'candidate.tm'),'checker_sha256':sha(Path(__file__)),'old_steps':408419,'new_steps':clock,'matched_checkpoints':408420,'right_neighbor_guard_visits':ng,'exceptional_visits':{f'{q}/{b}':vis[q,b]for q,b in spec},'endpoint_klabel':qn,'endpoint_canonical':M[qn],'head':hn,'header':header,'header_distance':header-hn,'physical_registers':vals[:9],'logical_registers':[vals[j]for j in[6,2,0,4,3,7,8,5,1]],'spare_values':vals[9:],'one_cells':sorted(newones),'all_other_cells_zero':True}
(OUT/'startup.json').write_text(json.dumps(res,indent=2)+'\n');print({k:v for k,v in res.items()if k not in('one_cells','spare_values')})
