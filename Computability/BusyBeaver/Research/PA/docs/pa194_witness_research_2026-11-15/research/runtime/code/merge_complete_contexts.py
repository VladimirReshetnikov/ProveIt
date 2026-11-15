#!/usr/bin/env python3
"""Union source/box windows and exact complete blank initialization windows."""
from pathlib import Path
import argparse,json,hashlib
p=argparse.ArgumentParser();p.add_argument('machine',type=Path);p.add_argument('source',type=Path);p.add_argument('boxes',type=Path);p.add_argument('output',type=Path);p.add_argument('--radius',type=int,default=6);p.add_argument('--startup-steps',type=int,default=57922);a=p.parse_args();K=a.radius
patterns={}
for src in(a.source,a.boxes):
 for ln in src.read_text().splitlines():
  q,v=map(int,ln.split());patterns.setdefault(q,set()).add(v)
rows={}
for ln in(a.machine/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=int(w),1 if d=='R'else-1,int(n)
before=sum(map(len,patterns.values()));q=74;head=0;ones=set()
for step in range(a.startup_steps):
 patterns.setdefault(q,set()).add(sum((head+i in ones)<<(i+K)for i in range(-K,K+1)))
 w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=d
assert(q,head)==(84,-2)
pc=json.loads((a.machine/'sites.json').read_text())[25][0]
if not isinstance(pc,str):pc=''.join(map(str,pc))
expected={-3,46};expected.update(-2+i for i,x in enumerate(pc)if x=='1')
physical=[0]*9;physical[6]=2;pos=47
for v in physical+[1]*26:
 pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
assert ones==expected,'Wrong complete startup frame'
states={q for q,b in rows};assert set(patterns)==states
text=''.join(f'{q} {v}\n'for q in sorted(patterns)for v in sorted(patterns[q]));a.output.write_text(text)
receipt=dict(machine=a.machine.name,radius=K,states=len(states),source_plus_box_contexts=before,contexts=sum(map(len,patterns.values())),additional_startup_contexts=sum(map(len,patterns.values()))-before,startup_steps=a.startup_steps,complete_startup_frame=True,sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Union of universal source nonbox windows, universal literal arithmetic-box windows with contextual list interiors, and every exact blank-startup window.')
a.output.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
