from pathlib import Path
from collections import Counter
import json,hashlib,itertools
H=Path(__file__).resolve().parent;D=H/'loop_delayed228'

import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)

def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 T={}
 for l in p.read_text().splitlines():
  if l and not l.startswith('#'):
   q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return T
O=table(D/'rotated229.klabels.tm');N=table(D/'candidate.klabels.tm');phi=lambda q:63 if q==79 else q
require(len(O)==458 and len(N)==456,'state count')
def inv(q,h,M):return (q not in(47,121,79)or M[h-1]==1)and(q!=63 or(M[h-1]==0 and M[h-2]==1))
count=0
for q in sorted({q for q,b in O}):
 for bits in itertools.product((0,1),repeat=4):
  mem=dict(zip(range(-3,1),bits))
  if not inv(q,0,mem):continue
  w,d,z=O[q,mem[0]];mem[0]=w;require(inv(z,d,mem),('invariant',q,bits,z));count+=1
require(all(0!=q for q in(47,121,79,63)),'initial guard')
def block(T,q,tag,b,n):
 M={-1:tag,0:b};h=0;tr=[]
 if tag==0:M[-2]=1
 for _ in range(n):
  require(h in M,'outside');r=M[h];w,d,z=T[q,r];tr.append([q,h,r,w,d,z]);M[h]=w;h+=d;q=z
 return(q,h,M),tr
blocks=[]
for q,tag in((63,0),(79,1)):
 for b in(0,1):
  a,ta=block(O,q,tag,b,1);dt=9 if(q,b)==(63,0)else 3;c,tc=block(N,phi(q),tag,b,dt);require(c==(phi(a[0]),a[1],a[2]),'block');blocks.append({'state':q,'bit':b,'tag':tag,'old':ta,'new':tc,'duration':dt})
ordinary=0
for(q,b),(w,d,z)in O.items():
 if q in(63,79):continue
 require(N[phi(q),b]==(w,d,phi(z)),'ordinary');ordinary+=1
(OUT/'fold_proof.json').write_text(json.dumps({'status':'ALL_TAPE_POSITIVE_BLOCK_FOLD_PASS','old_sha256':sha(D/'rotated229.klabels.tm'),'new_sha256':sha(D/'candidate.klabels.tm'),'inductive_cases':count,'ordinary_rows':ordinary,'blocks':blocks,'scope':'Every initial binary tape and head from common start0 for the rotated229-to228 fold only. Source rotation is separately justified.','checker_sha256':sha(Path(__file__))},indent=2)+'\n')
seed=json.loads((H/'delayed_erasure229/startup.json').read_text());goal=(84,seed['head'],set(seed['one_cells']))
def step(T,q,h,S):
 w,d,z=T[q,int(h in S)]
 if w:S.add(h)
 else:S.discard(h)
 return z,h+d
q=0;h=0;ones=set();ticks=None
for tick in range(1000001):
 if (q,h,ones)==goal:ticks=tick;break
 require(q!=230,'early halt')
 q,h=step(O,q,h,ones)
require(ticks is not None,'rotated229 seed not found')
q=qn=0;h=hn=0;ones=set();newones=set();clock=0;vis=Counter()
for tick in range(ticks):
 require((phi(q),h,ones)==(qn,hn,newones),('before',tick));key=q,int(h in ones);vis[key]+=1
 dt=9 if key==(63,0)else 3 if q in(63,79)else 1;q,h=step(O,q,h,ones)
 for _ in range(dt):qn,hn=step(N,qn,hn,newones)
 clock+=dt;require((phi(q),h,ones)==(qn,hn,newones),('after',tick))
require((qn,hn,newones)==goal,'end seed')
C=table(D/'candidate.canonical.tm');M={int(q):z for q,z in json.loads((D/'renumbering.json').read_text())['k_to_canonical'].items()};off=clock+1;mem=bytearray(2*clock+3);pos=off;st=0
for tick in range(clock):
 w,d,z=C[st,mem[pos]];mem[pos]=w;pos+=d;st=z
found={i-off for i,b in enumerate(mem)if b};require((st,pos-off,found)==(M[qn],hn,newones),'dense')
res={'status':'PASS_EXACT_BLANK_PREFIX_AND_INDEPENDENT_DENSE_CANONICAL_RUN','rotated229_sha256':sha(D/'rotated229.klabels.tm'),'klabels_sha256':sha(D/'candidate.klabels.tm'),'canonical_sha256':sha(D/'candidate.canonical.tm'),'engine_table_sha256':sha(D/'candidate.tm'),'checker_sha256':sha(Path(__file__)),'rotated_old_steps':ticks,'new_steps':clock,'matched_checkpoints':ticks+1,'exceptional_visits':{f'{q}/{b}':vis[q,b]for q in(63,79)for b in(0,1)},'endpoint_klabel':qn,'endpoint_canonical':M[qn],'head':hn,'header':seed['header'],'header_distance':seed['header_distance'],'physical_registers':seed['physical_registers'],'logical_registers':seed['logical_registers'],'spare_values':seed['spare_values'],'one_cells':sorted(newones),'all_other_cells_zero':True};(OUT/'startup.json').write_text(json.dumps(res,indent=2)+'\n');print({k:v for k,v in res.items()if k not in('one_cells','spare_values')})
