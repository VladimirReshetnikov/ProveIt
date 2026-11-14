#!/usr/bin/env python3
"""Independent literal source-frame proof replay for the H/X allocation."""
from pathlib import Path
import json,sys,hashlib,time
ROOT=Path(__file__).resolve().parent;OUT=ROOT/'evidence'
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT/'vendor'))
import independent_runtime as runtime
import symbolic_runtime as sym
import source_language as source
sym.HEADER_BASE=48
physical=(6,2,0,4,3,8,7,5,1)
rows={}
for l in (ROOT/'machine/pa194hx.native.tm').read_text().splitlines():
 q,b,w,d,t=l.split();rows[int(q),int(b)]=int(w),d,int(t)
states={q for q,b in rows}
assert len(states)==194 and len(rows)==388
mapping={int(k):v for k,v in json.loads((ROOT/'vendor/legacy_mapping.json').read_text()).items()}
for q in states|{254}:mapping.setdefault(q,q+10000)
assert len({mapping[q]for q in states|{254}})==195
table={(mapping[q],b):(w,1 if d=='R'else -1,mapping[t])for(q,b),(w,d,t)in rows.items()}
runtime.PHY=physical
lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
sites=json.loads((ROOT/'inputs/pa194.sites.json').read_text());ins=json.loads((ROOT/'inputs/pa194.instructions.json').read_text())
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
mapped=[[p,ops[o],a]for p,o,a in sites];graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'};assert [[names[e[0]]]+e[1:]+targets for e,targets in graph]==ins
contracts=[];total=maximum=0;started=time.monotonic()
for i,s in enumerate(mapped):
 for positive in ([False,True]if s[1]=='CD'else[False]):
  r=sym.case(table,lemmas,s,positive);total+=r['symbolic_steps'];maximum=max(maximum,r['symbolic_steps']);contracts.append({'site':i,'positive':positive,'duration':r['duration'],'motion':r['motion'],'symbolic_steps':r['symbolic_steps']})
 if(i+1)%1000==0:print('site',i+1,flush=True)
assert len(contracts)==4780
assert min(x['duration'][0]for x in contracts)>0
# Independent bytearray startup and full tape equality.
tape=bytearray(30000);origin=15000;head=origin;q=74
for step in range(56134):
 assert q!=254 and 0<=head<len(tape)
 w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R'else -1
assert q==84 and head-origin==-2
path=sites[25][0];frame=bytearray([1]+list(map(int,path))+[0]*(48-len(path))+[1]);logical=[2]+[0]*8;values=[None]*9
for i,j in enumerate(physical):values[j]=logical[i]
for value in values+[1]*26:frame.extend([0]+[1]*(value+1))
expected=bytearray(len(tape));first=head-1;expected[first:first+len(frame)]=frame;assert tape==expected
(OUT/'hx_contracts.json').write_text(json.dumps(contracts));(OUT/'hx_list_lemmas.json').write_text(json.dumps(blocks,indent=2));(OUT/'hx_seed.json').write_text(json.dumps(dict(q=q,head=head-origin,ones=[i-origin for i,b in enumerate(tape)if b],logical=logical,physical=values,spares=[1]*26),indent=2))
receipt=dict(status='PASS',states=194,source_sites=len(sites),contracts=len(contracts),symbolic_operations=total,max_operations=maximum,min_duration=min(x['duration'][0]for x in contracts),literal_list_lemmas=4,oracles=False,startup_steps=56134,full_tape_equal=True,source_graph_unchanged=True,physical_map=physical,seconds=time.monotonic()-started,scope='Relative physical source-frame simulation only; arithmetic calibration separate; no kernel proof')
(OUT/'hx_literal_receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
