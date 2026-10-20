#!/usr/bin/env python3
"""Fresh exact-table primitive census of the overloaded row36/read0."""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source218'))
from primitive_probe import Probe,rt,r
table=ROOT/'root218/candidate218/candidate.tm'
sites=json.loads((ROOT/'root218/candidate218/sites.json').read_text())
probe=Probe(r.b.read_table(table.read_bytes()));key=(probe.mp[36],0)
out=ROOT/'source218/row36_usage';out.mkdir(exist_ok=True)
def dump(name,x):(out/name).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
groups={}
for i,(pc,op,arg) in enumerate(sites):
 for pos in ((False,True) if op=='CD' else (False,)):
  groups.setdefault((op,arg,pos),(i,pos))
representatives=[]
for group,(i,pos) in groups.items():
 a=rt.case(probe.L,probe.lemmas,sites[i],pos)
 representatives.append({'op':group[0],'arg':group[1],'positive':pos,'index':i,'site':sites[i],
                         'uses36_0':key in a['rows']})
dump('representatives.json',representatives)
print('REPRESENTATIVES',json.dumps(representatives),flush=True)
counts=Counter();examples=defaultdict(list);cases=[];start=time.monotonic()
for i,site in enumerate(sites):
 for pos in ((False,True) if site[1]=='CD' else (False,)):
  a=rt.case(probe.L,probe.lemmas,site,pos)
  if key in a['rows']:
   group=f'{site[1]}{site[2]}:{int(pos)}';counts[group]+=1
   if len(examples[group])<5:examples[group].append({'index':i,'site':site,'positive':pos})
   cases.append([i,pos])
 if i%500==0:print('SOURCE',i,'uses',len(cases),'seconds',time.monotonic()-start,flush=True)
receipt={'status':'COMPLETE_PRIMITIVE_ROW_CENSUS','table_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),
         'row':[36,0],'cases_using_row':len(cases),'by_operator_guard':dict(counts),
         'examples':dict(examples),'cases':cases,'seconds':time.monotonic()-start,
         'scope':'Every source leaf and both decrement guards with independent arbitrary natural registers; no source reachability mask restriction.'}
dump('receipt.json',receipt)
print(json.dumps({k:v for k,v in receipt.items()if k not in('examples','cases')},indent=2),flush=True)
