"""Derive local windows from the independent literal execution, including boxes.
Discovery data only: positive candidates require fresh universal verification.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import json,sys,itertools,importlib.util,subprocess,time
HERE=Path(__file__).resolve().parent;K=5
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--package-root',type=Path,default=HERE.parents[1]);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
OUT=a.output;OUT.mkdir(parents=True,exist_ok=True);D=a.package_root/'machine';REF=a.package_root/'verification/reference'
sys.path.insert(0,str(REF))
spec=importlib.util.spec_from_file_location('literal_qh6',REF/'symbolic_runtime.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s);s.HEADER_BASE=48
rows={}
for ln in(D/'machine.native.tm').read_text().splitlines():
 q,b,w,d,t=ln.split();rows[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(t))
qs={q for q,b in rows};mapping={int(k):v for k,v in json.loads((REF/'legacy_mapping.json').read_text()).items()}
for q in qs|{254}:mapping.setdefault(q,q+10000)
inverse={v:q for q,v in mapping.items()};table={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in rows.items()}
patterns=defaultdict(set);seen=set()
@lru_cache(maxsize=100000)
def prefixes(atoms,k):
 if k==0:return ((),)
 if not atoms:return ((0,)*k,)
 a=atoms[0];tail=atoms[1:]
 if a[0]=='blank':return ((0,)*k,)
 if a[0]!='run':return tuple(itertools.product((0,1),repeat=k))
 _,b,coeff=a;const=coeff[0]
 assert all(c>=0 for c in coeff)
 if not any(coeff[1:]):
  if const>=k:return ((b,)*k,)
  return tuple((b,)*const+p for p in prefixes(tail,k-const))
 out=set()
 for length in range(min(const,k),k+1):
  if length>=k:out.add((b,)*k)
  else:
   for p in prefixes(tail,k-length):out.add((b,)*length+p)
 return tuple(out)
def collect(q,direction,left,right):
 q=inverse[q]
 if q not in qs:return
 lp=prefixes(tuple(left),K if direction==1 else K+1)
 rp=prefixes(tuple(right),K+1 if direction==1 else K)
 key=q,direction,lp,rp
 if key in seen:return
 seen.add(key)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a))+b if direction==1 else tuple(reversed(a[1:]))+(a[0],)+b
  patterns[q].add(sum(v<<i for i,v in enumerate(tape)))
old=s.State.step
def traced(self,table,lemmas,clock,motion):
 self.key();collect(self.q,self.direction,self.left,self.right)
 q,d,left,right=self.q,self.direction,self.left.copy(),self.right.copy()
 src=right if d==1 else left
 result=old(self,table,lemmas,clock,motion)
 event=result[2]
 if event[0]=='unary':
  b=event[1][1];w=event[1][2];const=event[2][0];variable=any(event[2][1:]);tail=src[1:]
  # Include every interior scan position; affine lengths are relaxed to all
  # natural lengths, and run correlations are discarded for discovery.
  for shifted in range(K+1):
   for remaining in range(1,K+2):
    if not variable and shifted+remaining!=const and shifted<K and remaining<K+1:continue
    new=( [s.run(w,shifted)]+left, [s.run(b,remaining)]+tail)if d==1 else([s.run(b,remaining)]+tail,[s.run(w,shifted)]+right)
    collect(q,d,*new)
 return result
s.State.step=traced
s.r.PHY=(6,2,0,4,3,7,8,5,1)
lemmas,proofs=s.prove_blocks(table)
sites=[[p,{'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[op],arg]for p,op,arg in json.loads((D/'sites.json').read_text())]
count=0
for i,site in enumerate(sites):
 for positive in ([False,True]if site[1]=='CD'else[False]):s.case(table,lemmas,site,positive);count+=1
 if(i+1)%1000==0:print('sites',i+1,flush=True)
seed=json.loads((D/'receipt.json').read_text())['startup'];q=74;head=0;ones=set()
for _ in range(seed['steps']):
 patterns[q].add(sum(int(head+i-K in ones)<<i for i in range(2*K+1)))
 w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=d
assert(q,head,ones)==(seed['state'],seed['head'],set(seed['one_cells']))
ctx=OUT/'QH6-all-contexts-k5.txt';ctx.write_text(''.join(f'{q} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
receipt={'source_outcomes':count,'states':len(patterns),'patterns':sum(map(len,patterns.values())),'contexts_per_state':{q:len(p)for q,p in patterns.items()},'runs':[]}
print('windows',receipt,flush=True)

(OUT/'literal-contexts-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
