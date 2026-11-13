#!/usr/bin/env python3
"""Verify dense conjugacy and derive the startup-protection row list."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
native=HERE/'candidate.native.tm'; dense=HERE/'dense.tm'; mapping=HERE/'dense-map.json'; original=HERE.parent/'allocator-screen/pa196.native.tm'; core=HERE.parent/'allocator-screen/protected-core.txt'
def need(b,msg):
 if not b:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
need(sha(native)=='9f8c37af1f206f17c5e6773df07a82d694b09454f295f53621fbb8ce00079f66','native SHA')
need(sha(dense)=='4ba0c5f88f9898d7765ce8107c25db65588f231a7825175037b077b3f4982db4','dense SHA')
need(sha(original)=='454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215','original SHA')
def read(p):
 table={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need(d in ('L','R') and (q,b) not in table,'row');table[q,b]=(w,1 if d=='R' else -1,z)
 return table
t=read(native);d=read(dense);labels=json.loads(mapping.read_text());need(len(labels)==197 and len(set(labels))==197 and labels[0]==74,'bijection');index={q:i for i,q in enumerate(labels)};index[254]=197
need(set(t)=={(q,b) for q in labels for b in (0,1)},'native domain')
need(d=={(index[q],b):(w,v,index[z]) for (q,b),(w,v,z) in t.items()},'conjugacy')
t=read(original);q=74;head=0;ones=set();used=set()
for _ in range(58154):
 key=(q,int(head in ones));used.add(key);w,direction,q=t[key]
 (ones.add if w else ones.discard)(head);head+=direction
protected={tuple(map(int,line.split())) for line in core.read_text().splitlines() if line.strip()};derived=protected|used
saved={tuple(map(int,line.split())) for line in (HERE/'protected-startup.txt').read_text().splitlines() if line.strip()}
need(len(used)==237 and len(protected)==98 and len(derived)==238 and saved==derived,'protection')
print('PASS: 197-state literal conjugacy; 237 startup rows + 98 core rows = 238 protected inputs')
