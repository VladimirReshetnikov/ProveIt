#!/usr/bin/env python3
"""Independent table export, census, label bijections and whole blank startup."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys
TH='4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651'
NH='3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'
SH='1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
PHY=(6,2,0,4,3,7,8,5,1)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def parse(p):
 t={};starts=[]
 for l in Path(p).read_text().splitlines():
  if l.startswith('#! start '):starts.append(int(l.split()[-1]))
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
   assert(q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R')
   t[q,b]=(w,1 if d=='R'else-1,z)
 assert starts==[0]
 return t

def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert sha(a.table)==TH and sha(a.source)==SH
 t=parse(a.table);states={q for q,b in t};assert len(t)==436 and len(states)==218
 assert set(t)=={(q,b)for q in states for b in(0,1)} and {z for w,d,z in t.values()}-states=={254}
 order=[0];mp={0:0}
 for q in order:
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
 assert set(mp)==states;mp[254]=218
 canonical={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
 labels={q:{102:301,120:302}.get(q,q)for q in states|{254}}
 native={(labels[q],b):(w,d,labels[z])for(q,b),(w,d,z)in t.items()}
 assert len(set(labels.values()))==219
 a.output.mkdir(parents=True,exist_ok=True)
 (a.output/'k218.tm').write_bytes(encode(canonical));(a.output/'k218.native.tm').write_bytes(encode(native))
 assert sha(a.output/'k218.native.tm')==NH
 steps=312701;ones=set();q=h=0;visits=Counter()
 for _ in range(steps):
  b=int(h in ones);visits[q,b]+=1;w,d,q=t[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 dense=bytearray(2*steps+3);origin=steps+1;head=origin;state=0;counts=Counter()
 for _ in range(steps):
  b=dense[head];counts[state,b]+=1;w,d,state=canonical[state,b];dense[head]=w;head+=d
 logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 expected={-6,139};pos=140
 for value in physical+[1]*130:
  pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
 assert(q,h,ones)==(84,-5,expected)
 assert(state,head-origin,{i-origin for i,b in enumerate(dense)if b})==(mp[84],-5,expected)
 assert counts==Counter({(mp[q],b):v for(q,b),v in visits.items()})
 result=dict(status='EXACT_218_CENSUS_BIJECTIONS_AND_COMPLETE_STARTUP_PASS',working_states=218,rows=436,start=0,normalized_halt=254,canonical_halt=218,all_working_states_graph_reachable=True,normalized_sha256=TH,native_sha256=NH,source_sha256=SH,canonical_sha256=sha(a.output/'k218.tm'),normalized_to_canonical=mp,canonical_to_normalized={v:k for k,v in mp.items()},normalized_to_native=labels,native_to_normalized={v:k for k,v in labels.items()},startup=dict(steps=steps,normalized_state=q,canonical_state=state,head=h,one_cells=sorted(ones),all_other_cells=0,logical_registers=logical,physical_registers=physical,logical_to_physical=PHY,header=139,extra_gap=80,spares=[1]*130,sparse_and_dense_agree=True))
 dump(a.output/'canonicalization.json',result);print(result['status'],result['canonical_sha256'])
if __name__=='__main__':main()
