#!/usr/bin/env python3
"""Independent literal marker lemma, exact dense isomorphism and complete blank run."""
from pathlib import Path
import json,hashlib,argparse,gzip
from reconstruct216 import table
ROOT=Path(__file__).resolve().parent.parent
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 O=table(ROOT/'machine/prefold217.native.tm');N=table(ROOT/'machine/k216.native.tm');C=table(ROOT/'machine/k216.tm');Q={q for q,b in O};R={q for q,b in N};assert len(Q)==217 and len(R)==216 and R==Q-{183}
 assert len(N)==432 and {z for w,d,z in N.values()}-R=={254}
 phi=lambda q:164 if q==183 else q
 incoming={q:[(x,b,w,d)for(x,b),(w,d,z)in O.items()if z==q]for q in(164,183)}
 for q,marker in((164,1),(183,0)):
  assert q!=0 and incoming[q]and all(w==marker and d=='R'for x,b,w,d in incoming[q])
 assert O[164,0]==(0,'R',77)and O[183,0]==(0,'R',150)and O[164,1]==O[183,1]==(1,'R',98)
 assert N[164,0]==(0,'L',201)and N[164,1]==(1,'R',98)
 assert N[201,0]==(0,'R',195)and N[201,1]==(1,'R',196)and N[195,0]==(0,'R',150)and N[196,0]==(0,'R',77)
 for(q,b),(w,d,z)in O.items():
  if(q,b)not in((164,0),(183,0)):assert N[phi(q),b]==(w,d,phi(z))
 # The loop checks EVERY unchanged edge, including all control/initial edges.
 # An entry writes the origin at h-1. The zero-trigger three-step block restores
 # this bit, reads the unchanged trigger zero, and joins the old one-step result.
 # All outside cells are untouched. Common-one transitions coincide. All blocks
 # are positive, proving forward and reverse halting preservation for all tapes.
 m={int(k):v for k,v in json.loads((ROOT/'machine/canonicalization.json').read_text())['native_to_canonical'].items()}
 assert len(m)==len(set(m.values()))==217 and set(m)==R|{254}and set(m.values())==set(range(217))and m[0]==0 and m[254]==216
 assert {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in N.items()}==C
 reachable={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   z=N[q,b][2]
   if z!=254 and z not in reachable:reachable.add(z);todo.append(z)
 assert reachable==R
 startup=json.loads(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes()))
 assert(startup['steps'],startup['state'],startup['head'],startup['gap'],startup['registers'],startup['spares'])==(313133,84,-5,80,[3,0,0,0,3,0,0,0,0],[1]*130)
 for name,T,dispatch in(('native',N,84),('canonical',C,m[84])):
  q,h=0,0;ones=set()
  for step in range(313133):
   b=int(h in ones);w,d,z=T[q,b];direction=1 if d=='R'else-1
   if name=='native':assert startup['trace'][step]==[q,h,b,w,direction,z]
   if w:ones.add(h)
   else:ones.discard(h)
   q=z;h+=direction
  assert(q,h)==(dispatch,-5)and sorted(ones)==startup['one_cells']and len(ones)==277
 # Independently decode the entire finite nonzero support; outside it is zero.
 ones=set(startup['one_cells']);head=-5;assert min(ones)==head-1
 header=min(x for x in ones if x>head-1);assert header==head+64+80
 p=header+1;values=[]
 while p<=max(ones):
  assert p not in ones and p+1 in ones;p+=1;v=0
  while p in ones:v+=1;p+=1
  values.append(v-1)
 assert len(values)==139 and [values[i]for i in(6,2,0,4,3,7,8,5,1)]==startup['registers']and values[9:]==startup['spares']
 r={'status':'MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS','working_states':216,'rows':432,'graph_reachable_working_states':216,'blank_steps':313133,'head':-5,'native_dispatch':84,'canonical_dispatch':m[84],'one_cells':sorted(ones),'incoming_origin_guards':incoming,'scope':'All tapes for marker fold; exact finite blank startup with complete exterior; not a proof-assistant endpoint.'}
 a.out.write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
if __name__=='__main__':main()
