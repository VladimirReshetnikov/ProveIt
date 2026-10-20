#!/usr/bin/env python3
"""Probe transported2/8 leaf entries and synthesize the conflicting123/0 row."""
from pathlib import Path
import hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source218'));from primitive_probe import Probe,rt,r
folder=ROOT/'source218/rename28/published'
T=r.b.read_table((folder/'candidate218.tm').read_bytes());sites=json.loads((folder/'sites.json').read_text())
p=Probe(T);groups={}
for i,(pc,op,arg)in enumerate(sites):
 for pos in((False,True)if op=='CD'else(False,)):groups.setdefault((op,arg,pos),(i,pos))
checks=[]
for group,(i,pos)in groups.items():
 try:
  a=p.case(p.L,p.lemmas,sites[i],pos);status='PASS';error=None
 except Exception as e:status='FAIL';error=str(e)[:700]
 checks.append({'index':i,'site':sites[i],'positive':pos,'status':status,'error':error})
(folder/'representative_interfaces.json').write_text(json.dumps(checks,indent=2)+'\n')
print('INITIAL',json.dumps(checks),flush=True)
key=(p.mp[123],0);actions=[(w,d,z)for w in(0,1)for d in(-1,1)for z in sorted({q for q,b in T}|{254})]
chosen=[(9,False),(9,True),(90,False),(57,False),(43,False),(43,True)]
survivors=[];counts=[0]*len(chosen);start=time.monotonic()
for count,action in enumerate(actions):
 U=dict(p.L);w,d,z=action;U[key]=(w,d,p.mp[z]);ok=True
 for j,(i,pos)in enumerate(chosen):
  try:p.case(U,p.lemmas,sites[i],pos)
  except Exception:ok=False;break
  counts[j]+=1
 if ok:
  N=dict(T);N[123,0]=action;name=folder/f'row123_survivor_{len(survivors):03d}.tm';name.write_bytes(r.b.table_bytes(N))
  survivors.append({'action':action,'table':str(name.relative_to(ROOT))});print('SURVIVOR',survivors[-1],flush=True)
 if count%100==0:print('TRIALS',count,'counts',counts,'seconds',time.monotonic()-start,flush=True)
receipt={'status':'COMPLETE_FINITE_ONE_ROW_INTERFACE_SCREEN','row':[123,0],'actions':len(actions),'cases':chosen,
         'prefix_survivor_counts':counts,'survivors':survivors,'seconds':time.monotonic()-start,
         'scope':'Each accepted literal-PC probe is universal in all natural primary registers; untested full-source cases and startup remain separate. A negative result is limited to one changed literal row and1000 symbolic proof steps.'}
(folder/'row123_screen.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
