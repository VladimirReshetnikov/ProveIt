#!/usr/bin/env python3
"""All-tape marker proof, exact canonical isomorphism, and complete blank replay."""
from pathlib import Path
import argparse,json,gzip
from reconstruct215 import table
ROOT=Path(__file__).resolve().parent.parent
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--variant',choices=('210','120'),default='210');a=ap.parse_args();config=json.loads((ROOT/'code/variants.json').read_text())[a.variant];D=ROOT/config['directory']
 O=table(D/'machine/prefold216.native.tm');N=table(D/'machine/k215.native.tm');C=table(D/'machine/k215.tm');Q={q for q,b in O};R={q for q,b in N};assert len(Q)==216 and len(R)==215 and R==Q-{183}
 assert len(N)==430 and {z for w,d,z in N.values()}-R=={254}
 phi=lambda q:164 if q==183 else q
 incoming={q:[(x,b,w,d)for(x,b),(w,d,z)in O.items()if z==q]for q in(164,183)}
 for q,marker in((164,1),(183,0)):assert q!=0 and incoming[q]and all(w==marker and d=='R'for x,b,w,d in incoming[q])
 assert O[164,0]==(0,'R',77)and O[183,0]==(0,'R',150)and O[164,1]==O[183,1]==(1,'R',98)
 assert N[164,0]==(0,'L',195)and N[164,1]==(1,'R',98)
 assert N[195,0]==(0,'R',181)and N[195,1]==(1,'R',196)and N[181,0]==(0,'R',150)and N[196,0]==(0,'R',77)
 for(q,b),(w,d,z)in O.items():
  if(q,b)not in((164,0),(183,0)):assert N[phi(q),b]==(w,d,phi(z))
 # All nonfold steps commute. Every entry to either merged state writes its
 # origin marker on the left. Only h-1,h are read by the following positive
 # 1-or-3-step block, so arbitrary exterior tape is untouched.
 for q,marker in((164,1),(183,0)):
  for bit in(0,1):
   memory={-1:marker,0:bit};w,d,z=O[q,bit];expected=(phi(z),1,{-1:marker,0:w});qq=164;hh=0
   for j in range(3 if bit==0 else 1):
    assert hh in memory;w,d,qq=N[qq,memory[hh]];memory[hh]=w;hh+=1 if d=='R'else-1
   assert(qq,hh,memory)==expected
 m={int(k):v for k,v in json.loads((D/'machine/canonicalization.json').read_text())['native_to_canonical'].items()}
 assert len(m)==len(set(m.values()))==216 and set(m)==R|{254}and set(m.values())==set(range(216))and m[0]==0 and m[254]==215
 assert {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in N.items()}==C
 reachable={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   z=N[q,b][2]
   if z!=254 and z not in reachable:reachable.add(z);todo.append(z)
 assert reachable==R
 startup=json.loads(gzip.decompress((D/'evidence/startup.json.gz').read_bytes()));steps=config['startup_steps']
 assert(startup['steps'],startup['state'],startup['head'],startup['gap'],startup['registers'],startup['spares'])==(steps,84,-8,1,[4,0,0,0,0,0,0,0,0],[1]*40)
 for name,T,dispatch in(('native',N,84),('canonical',C,m[84])):
  q,h=0,0;ones=set()
  for step in range(steps):
   b=int(h in ones);w,d,z=T[q,b];direction=1 if d=='R'else-1
   if name=='native':assert startup['trace'][step]==[q,h,b,w,direction,z]
   if w:ones.add(h)
   else:ones.discard(h)
   q=z;h+=direction
  assert(q,h)==(dispatch,-8)and sorted(ones)==startup['one_cells']and len(ones)==95
 # Decode complete support independently. In particular the PC is exactly0;
 # merely recognizing an internal dispatcher frame is not sufficient.
 ones=set(startup['one_cells']);head=-8;assert min(ones)==head-1
 header=min(x for x in ones if x>head-1);assert header==57==head+64+1
 p=header+1;values=[]
 while p<=max(ones):
  assert p not in ones and p+1 in ones;p+=1;v=0
  while p in ones:v+=1;p+=1
  values.append(v-1)
 assert len(values)==49 and [values[i]for i in(6,2,0,4,3,7,8,5,1)]==startup['registers']and values[9:]==startup['spares']
 r={'status':'MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS','variant':a.variant,'working_states':215,'rows':430,'graph_reachable_working_states':215,'blank_steps':steps,'head':-8,'native_dispatch':84,'canonical_dispatch':m[84],'one_cells':sorted(ones),'incoming_origin_guards':incoming,'scope':'All tapes for marker fold; exact finite blank startup with complete exterior; not a proof-assistant endpoint.'}
 a.out.write_text(json.dumps(r,indent=2)+'\n');print(r['status'],a.variant)
if __name__=='__main__':main()
