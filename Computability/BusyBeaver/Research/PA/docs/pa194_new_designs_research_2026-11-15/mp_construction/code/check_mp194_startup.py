#!/usr/bin/env python3
"""Independent complete finite-support tape check of MP194 blank startup."""
from pathlib import Path
import argparse,json,hashlib,collections
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('sites',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
rows={}
for ln in a.table.read_text().splitlines():
 q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t));assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R');rows[q,b]=(w,1 if d=='R'else-1,t)
states={q for q,b in rows};assert len(states)==194 and len(rows)==388 and 254 not in states
assert set(rows)=={(q,b)for q in states for b in(0,1)}
assert {n for w,d,n in rows.values()}-states=={254}
sites=json.loads(a.sites.read_text());head=-2;pc=sites[25][0]
expected={head-1,head+48}|{head+i for i,b in enumerate(pc)if b=='1'};pos=head+49
physical=[0,0,0,0,0,0,2,0,0];spares=[1]*26
for value in physical+spares:
 pos+=1;expected.update(range(pos,pos+value+1));pos+=value+1
q,h,ones=74,0,set()
for step in range(58067):
 if(q,h,ones)==(84,-2,expected):break
 assert q!=254,'early halt'
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
else:raise AssertionError('complete seed not reached')
assert step==58066
seed={'state':q,'head':h,'ones':sorted(ones)}
seen={74};todo=collections.deque([74])
while todo:
 q=todo.popleft()
 for b in(0,1):
  n=rows[q,b][2]
  if n!=254 and n not in seen:seen.add(n);todo.append(n)
assert seen==states
rec={'status':'PASS','native_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(a.sites.read_bytes()).hexdigest(),'working_states':194,'transition_rows':388,'all_working_states_graph_reachable':True,'native_start':74,'native_halt':254,'startup_steps':step,'seed_source_site':25,'seed_source_path':pc,'seed':seed,'physical_registers':physical,'spares':spares,'header_distance':48,'complete_tape_equality':True,'zero_exterior':True}
if a.output:a.output.write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items()if k not in('seed','spares')},indent=2))
