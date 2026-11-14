#!/usr/bin/env python3
"""Independent literal-table checks of source_reduction outputs; no compiler imports."""
from pathlib import Path
import json,hashlib,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
import source_language as source
sym.HEADER_BASE=48
assert __debug__
PHY=(6,2,0,4,3,7,8,5,1)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def check(path):
 data=json.loads((path/'receipt.json').read_text());rows={}
 for line in(path/'machine.native.tm').read_text().splitlines():
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert(q,b)not in rows;rows[q,b]=(w,d,t)
 states={q for q,b in rows};assert len(states)==194 and len(rows)==388
 assert set(rows)=={(q,b)for q in states for b in(0,1)}
 assert{t for w,d,t in rows.values()}-states=={254}
 labels=json.loads((path/'labels.json').read_text())
 assert len(labels)==len(set(labels))==195 and labels[0]==74 and labels[-1]==254
 assert set(labels[:-1])==states
 dense={}
 for line in(path/'machine.tm').read_text().splitlines():
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  assert(q,b)not in dense and 0<=q<194 and b in(0,1)and w in(0,1)and d in('L','R')and 0<=t<=194
  dense[q,b]=(w,d,t)
 assert len(dense)==388
 assert{(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in dense.items()}==rows
 mapped=[[p,{'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[op],arg]for p,op,arg in json.loads((path/'sites.json').read_text())]
 graph,_=source.graph_arithmetic(mapped);assert graph==source.graph_intervals(mapped)
 names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
 ins=[[names[e[0]]]+e[1:]+targets for e,targets in graph]
 assert ins==json.loads((path/'instructions.json').read_text())
 mapping={int(k):v for k,v in json.loads((HERE/'reference/legacy_mapping.json').read_text()).items()}
 for q in states|{254}:mapping.setdefault(q,q+10000)
 assert len({mapping[q]for q in states|{254}})==195 and mapping[84]==96
 table={(mapping[q],b):(w,1 if d=='R'else-1,mapping[t])for(q,b),(w,d,t)in rows.items()}
 runtime.PHY=PHY;lemmas,blocks=sym.prove_blocks(table);assert len(blocks)==4
 contracts=[];total=maximum=0
 for i,site in enumerate(mapped):
  for positive in([False,True]if site[1]=='CD'else[False]):
   out=sym.case(table,lemmas,site,positive);total+=out['symbolic_steps'];maximum=max(maximum,out['symbolic_steps'])
   contracts.append(dict(site=i,positive=positive,**out))
  if(i+1)%1000==0:print(path.name,'checked',i+1,flush=True)
 tape=bytearray(20000);head=10000;q=74
 for step in range(data['startup']['steps']):
  assert q!=254 and 0<=head<len(tape)
  w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d=='R'else-1
 assert(q,head)==(84,9998)
 logical=[2]+[0]*8;physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 p=mapped[25][0];frame=bytearray([1]+[int(b)for b in p]+[0]*(48-len(p))+[1])
 for v in physical+[1]*26:frame.extend([0]+[1]*(v+1))
 expect=bytearray(len(tape));expect[head-1:head-1+len(frame)]=frame;assert tape==expect
 outdir=path/'independent';outdir.mkdir(exist_ok=True)
 raw=json.dumps(contracts,separators=(',',':'),default=lambda x:sorted(x)if isinstance(x,set)else str(x)).encode();(outdir/'contracts.json').write_bytes(raw)
 (outdir/'list_lemmas.json').write_text(json.dumps(blocks,indent=2,default=lambda x:sorted(x)if isinstance(x,set)else str(x))+'\n')
 receipt=dict(family=path.name,status='PASS',states=194,rows=388,source_sites=len(mapped),source_outcomes=len(contracts),
  symbolic_steps=total,maximum_symbolic_steps=maximum,minimum_positive_duration_constant=min(x['duration'][0]for x in contracts),
  list_lemmas_from_literal_table=4,box_oracles=False,independent_source_resolvers_agree=True,dense_native_conjugacy=True,whole_blank_startup=True,startup_steps=data['startup']['steps'],
  dense_sha256=sha((path/'machine.tm').read_bytes()),native_sha256=sha((path/'machine.native.tm').read_bytes()),contracts_sha256=sha(raw),
  scope='Nine arbitrary natural primary registers, both decrement branches, arbitrary nonempty finite spare list and affine gap. Not a new Lean or end-to-end PA proof compiler.')
 (outdir/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
for arg in sys.argv[1:]:check(Path(arg))
