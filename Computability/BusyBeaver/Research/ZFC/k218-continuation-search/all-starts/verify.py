#!/usr/bin/env python3
"""Independent exact finite prefixes plus one-row blank-ray obligations."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
T={}
for line in (R/'core217.native.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();key=(int(q),int(b));assert key not in T;T[key]=(int(w),1 if d=='R'else-1,int(z))
Q={q for q,b in T};assert len(Q)==217 and len(T)==434 and 254 not in Q
rows=[json.loads(l)for l in (R/'all-starts.jsonl').read_text().splitlines()];assert {r['start']for r in rows}==Q-{0} and len(rows)==216
proved=[]
for r in rows:
 assert r['status']=='UNCONDITIONAL_ZERO_RAY'and not r['observations']
 q=r['start'];h=0;ones=set()
 for tick in range(r['steps']):
  assert q!=254
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 assert(q,h,len(ones))==(r['state'],r['head'],r['ones_count'])
 assert h not in ones
 w,d,z=T[q,0];assert z==q
 assert all((x<h if d==1 else x>h)for x in ones)
 proved.append({'start':r['start'],'prefix_steps':r['steps'],'state':q,'head':h,'ones':sorted(ones),'ray_action':[w,d,z],'scope':'After the prefix, every next scanned cell is0 and the state is unchanged forever; arbitrary written bits lie behind the head.'})
# Reuse, rather than rerun, the exact retained start0 prefix.
P=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k218/research/failed-delete301-prefix.json');old=json.loads(P.read_text())
assert len(old['finite_trace'])==85
for tick,q,h,b,w,d,z in old['finite_trace']:assert T[q,b]==(w,d,z)
assert old['finite_prefix']['state']==35 and old['finite_prefix']['head']==7 and old['finite_prefix']['one_cells']==[-3,-2] and T[35,0]==(1,1,35)
proved.append({'start':0,'prefix_steps':85,'state':35,'head':7,'ones':[-3,-2],'ray_action':[1,1,35],'scope':'Exact85-row transfer from previously preserved complete blank trace and infinite-ray argument.'})
assert {r['start']for r in proved}==Q
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result={'status':'ALL_217_WORKING_START_STATES_HAVE_ZERO_RAY_PROOFS','table_sha256':sha(R/'core217.native.tm'),'working_states':217,'new_prefixes_independently_replayed':216,'new_literal_transitions':sum(r['steps']for r in rows),'transferred_start0_prefix_steps':85,'maximum_prefix_steps':max(r['prefix_steps']for r in proved),'all_initial_tapes_claimed':False,'initial_tape':'all0; head0; every allowed working start state','source_binding':'This exact table is K218 with301deleted and87/0→0R88,88/0→0L51,51/0→0R122. No arbitrary initializer or further row change is ruled out.','induction':'For each witness, scanned0 self-loop writesw and movesd into a half-line containing no1. At every later time the same row applies; written cells are left behind. Therefore there is no halt.','control':'C++ detector reproduces the exact accepted K218 start0 frame at312909; this finite observation is separate from the ray proofs.','inputs':{n:sha(R/n)for n in ['search.cpp','search','all-starts.jsonl','all-starts.log','control.jsonl','control.log','verify.py']},'start0_source_receipt':{'path':str(P),'sha256':sha(P)},'proofs':sorted(proved,key=lambda x:x['start'])}
(R/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('proofs','inputs')},indent=2))
