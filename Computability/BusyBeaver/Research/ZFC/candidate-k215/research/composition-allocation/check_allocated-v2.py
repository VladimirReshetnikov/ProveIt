#!/usr/bin/env python3
"""Own finite whole-prefix/local-entry audit of held allocation; no allocator/runtime invocation."""
from pathlib import Path
from collections import defaultdict
import json,hashlib
import source_language as s
import build221 as b
P=Path(__file__).resolve().parent
K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k216')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=P/'sites-210.json';machine=P/'allocation210-run2/candidate.native.tm';record=P/'allocation210-run2/allocation.json'
assert sha(source)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
assert sha(machine)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
old=s.tree(json.loads((K/'sites216.json').read_text()));new=s.tree(json.loads(source.read_text()))
T=b.read_table((K/'k216.native.tm').read_bytes());N=b.read_table(machine.read_bytes());rec=json.loads(record.read_text())
assert rec['status']=='PREFIX_FAIL'and len(rec['binding_failures'])==8
O,op=b.decoder_map(T,old);G,gp=b.decoder_map(N,new)
oldrole=defaultdict(set);acts=defaultdict(set)
for q,ns in O.items():
 for n in ns:
  oldrole[n].add(q)
  for bit,ch in enumerate(n):
   if s.leaf(ch):acts[ch,bit].add(T[q,bit])
for op,arg,q in [('CC',1,1),('CC',2,16),('CB',1,302)]:
 if((op,arg),1)in acts:acts[(op,arg),1].add((0,-1,q))
assignments={s.subtree(new,e['path']):e['q']for e in rec['assignments']}
paths={p:q for q,ps in gp.items()for p in ps};oldalias=[];leafentries=0;freshentries=0
for p,q in sorted(paths.items()):
 n=s.subtree(new,p)
 assert q in oldrole.get(n,())or assignments.get(n)==q,(p,q,'no exact source role')
 # Every prefix is also checked from the actual dispatcher, independently of
 # the recursive first-edge walk in decoder_map.
 tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);h=0;z=84
 for _ in range(10000):
  if h==len(p):break
  assert h in tape and(z,tape[h])in N
  w,d,z=N[z,tape[h]];tape[h]=w;h+=d
 assert(h,z,tape)==(len(p),q,before),(p,q,h,z)
 for bit,ch in enumerate(n):
  if not s.leaf(ch):continue
  leafentries+=1
  if q in oldrole.get(n,()):
   if(q,bit)==(81,0):assert T[q,bit]==(0,-1,92) and N[q,bit]==(0,-1,111)
   else:assert N[q,bit]==T[q,bit],(p,q,bit,'changed retained entry')
  else:
   freshentries+=1;assert N[q,bit]in acts[ch,bit],(p,q,bit,ch,N[q,bit])
  if q==108 and bit==1:
   suffix={'CC':'101','CB':'001'}[ch[0]]
   assert('1'+p+'1').endswith(suffix),(p,ch,'contextual108')
   oldalias.append({'path':p,'state':q,'node':n,'entry':N[q,bit],'required_suffix':suffix})
assert leafentries==4751
repair=[]
for marker in(0,1):
 ends=[]
 for tab in(T,N):
  tape={-1:marker,0:0};h=0;q=81;trace=[]
  for step in range(3):
   trace.append([q,h,tape[h]]);w,d,q=tab[q,tape[h]];tape[h]=w;h+=d
  ends.append((q,h,tape));
 assert ends[0]==ends[1]==(123 if marker==0 else21,1,{-1:marker,0:0})
 repair.append({'marker':marker,'steps':3,'final_state':ends[0][0],'head':1,'tape_unchanged':True})
# Explain precisely the failed global-only gate: all8 are unchanged old108
# entries under101; no candidate/source bytes or interpreter rules changed.
failed={e['path']for e in rec['binding_failures']}
assert failed=={e['path']for e in oldalias if e['node']==(('CD',6),('CC',2))}
assert all(e['state']==108 and e['allowed']==[13] and not e['tape_changed']for e in rec['binding_failures'])
# Both retained selector packages and the locally proved81 repair survive.
expected={(69,0):(0,-1,213),(69,1):(1,1,31),(213,0):(0,1,92),(213,1):(1,1,90),(92,0):(0,1,104),(90,0):(0,1,105),(164,0):(0,-1,201),(164,1):(1,1,98),(201,0):(0,1,195),(201,1):(1,1,196),(195,0):(0,1,150),(196,0):(0,1,77),(81,0):(0,-1,111),(111,0):(0,1,104),(111,1):(1,1,128),(104,0):(0,1,123),(128,0):(0,1,21)}
assert all(N[k]==v for k,v in expected.items())
assert len(N)==430 and len({q for q,_ in N})==215
identity=json.loads((P/'identity-run1/allocation.json').read_text())
assert identity['status']=='PREFIX_PASS'and identity['states']==216 and identity['new_nodes']==0
assert identity['changed_rows']==[[81,0,0,-1,111]]
result={'status':'HELD_TABLE_PREFIX_AND_LITERAL_ENTRY_PASS','scope':'Finite exact source-word/CFG composition and complete4750 internal-prefix+4751 literal primitive entry correspondence, including8 local108 aliases. No primitive runtime, blank startup, all-natural calibration composition or215candidate acceptance claimed.','states':215,'rows':430,'source_metrics':s.metrics(new),'internal_prefixes':len(paths),'leaf_entries':leafentries,'fresh_leaf_entries':freshentries,'strict_global_gate_failure_preserved':str(record),'local_alias_correction':oldalias,'identity_control':'216states, exact unchanged source and only independently justified81/0repair; no allocation.','local81_three_step_whole_tape_blocks':repair,'selector_rows':[[*k,*v]for k,v in expected.items()],'inputs':{str(p):sha(p)for p in[source,machine,record,Path(__file__),P/'allocate-v1.py',P/'allocate-v2.py',P/'identity-run1/allocation.json',P/'result.json',P/'source_language.py',P/'build221.py']}}
(P/'held-candidate-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
