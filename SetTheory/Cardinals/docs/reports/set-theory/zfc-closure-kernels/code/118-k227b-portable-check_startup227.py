from pathlib import Path
import json,hashlib,sys
H=Path(__file__).resolve().parent;D=H/'source_fold227_zerofix'
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)

def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 T={};starts=[]
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):starts.append(int(l[9:]))
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 require(starts==[0],'initial state');return T
T=table(D/'candidate.klabels.tm');C=table(D/'candidate.canonical.tm');config=json.loads((D/'construction.json').read_text());require(config['klabels_sha256']==sha(D/'candidate.klabels.tm')and config['canonical_sha256']==sha(D/'candidate.canonical.tm'),'input changed');M={int(q):z for q,z in json.loads((D/'renumbering.json').read_text())['k_to_canonical'].items()};require(C=={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in T.items()},'relabel')
seed=json.loads((H/'loop_delayed228/startup.json').read_text());ones=set();q=h=0;target=set(seed['one_cells']);found=None
for n in range(1000001):
 if(q,h,ones)==(84,seed['head'],target):found=n;break
 require(q!=230,'early halt');w,d,z=T[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=z
require(found is not None,'complete seed not found')
off=found+1;mem=bytearray(2*found+3);pos=off;st=0
for n in range(found):
 w,d,z=C[st,mem[pos]];mem[pos]=w;pos+=d;st=z
require((st,pos-off,{i-off for i,b in enumerate(mem)if b})==(M[q],h,ones),'dense canonical disagreement')
res={'status':'PASS_EXACT_SPARSE_AND_DENSE_CANONICAL_BLANK_STARTUP','klabels_sha256':sha(D/'candidate.klabels.tm'),'canonical_sha256':sha(D/'candidate.canonical.tm'),'engine_table_sha256':sha(D/'candidate.tm'),'new_steps':found,'endpoint_klabel':q,'endpoint_canonical':M[q],'head':h,'header':seed['header'],'header_distance':seed['header_distance'],'physical_registers':seed['physical_registers'],'logical_registers':seed['logical_registers'],'spare_values':seed['spare_values'],'one_cells':sorted(ones),'all_other_cells_zero':True,'seed_reference_sha256':sha(H/'loop_delayed228/startup.json'),'checker_sha256':sha(Path(__file__))};(OUT/'startup.json').write_text(json.dumps(res,indent=2)+'\n');print({k:v for k,v in res.items()if k not in('one_cells','spare_values')})
