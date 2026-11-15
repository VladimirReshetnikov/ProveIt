#!/usr/bin/env python3
"""Independent arbitrary-register/list verification for a native table and source sites."""
from pathlib import Path
import argparse,json,hashlib,time
import symbolic_runtime as s
H=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('sites',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
mapping={int(k):v for k,v in json.loads((H/'legacy_mapping.json').read_text()).items()}
rows={}
for ln in a.table.read_text().splitlines():
 q,b,w,d,t=ln.split();q,b,w,t=map(int,(q,b,w,t));mapping.setdefault(q,q+10000);mapping.setdefault(t,t+10000);rows[q,b]=(w,1 if d=='R'else-1,t)
assert len({mapping[q]for q in {k[0]for k in rows}|{254}})==len(rows)//2+1
assert mapping[84]==96 and mapping[254]==254
table={(mapping[q],b):(w,d,mapping[t])for(q,b),(w,d,t)in rows.items()};s.HEADER_BASE=48
lemmas,proofs=s.prove_blocks(table)
(a.output/'list_lemmas.json').write_text(json.dumps(proofs,indent=2)+'\n')
seen=set();oldstep=s.State.step
def step(st,*args):
 q,d,l,r=st.key();key=q,d,tuple(l),tuple(r)
 if key in seen:raise AssertionError('Exact symbolic configuration cycle')
 seen.add(key);return oldstep(st,*args)
s.State.step=step
sites=json.loads(a.sites.read_text());opcodes={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
cts=[];start=time.time();tot=0;mx=0;mn=None
for i,(pc,op,arg)in enumerate(sites):
 if not isinstance(pc,str):pc=''.join(map(str,pc))
 for pos in([False,True]if op=='dec'else[False]):
  seen.clear()
  try:r=s.case(table,lemmas,(pc,opcodes[op],arg),pos)
  except(AssertionError,KeyError)as e:
   result={'status':'FAIL','site':i,'source':[pc,op,arg],'positive':pos,'passed_contracts':len(cts),'error':str(e),'seconds':time.time()-start};(a.output/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True);raise SystemExit(1)
  tot+=r['symbolic_steps'];mx=max(mx,r['symbolic_steps']);mn=r['duration'][0]if mn is None else min(mn,r['duration'][0]);cts.append({'site':i,'positive':pos,'symbolic_steps':r['symbolic_steps'],'duration':r['duration'],'motion':r['motion']})
 if i%500==0:print('checked',i,'contracts',len(cts),'seconds',round(time.time()-start,2),flush=True)
(a.output/'contracts.json').write_text(json.dumps(cts,separators=(',',':'))+'\n')
result={'status':'PASS','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(a.sites.read_bytes()).hexdigest(),'working_states':len(rows)//2,'sites':len(sites),'contracts':len(cts),'symbolic_steps':tot,'maximum_symbolic_steps':mx,'minimum_positive_duration_constant':mn,'list_lemmas':4,'kernel_checked':False,'scope':'universal prescribed source instruction contracts with arbitrary natural registers and arbitrary finite spare lists; no blank startup or consistency calibration is claimed','seconds':time.time()-start}
(a.output/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
