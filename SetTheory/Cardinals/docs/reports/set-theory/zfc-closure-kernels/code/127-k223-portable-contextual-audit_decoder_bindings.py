#!/usr/bin/env python3
"""Independent exact table, label-map, source DAG, and decoder-edge audit."""
from pathlib import Path
from collections import Counter
import hashlib,json
H=Path(__file__).resolve().parent;D=H.parent/'fold_binding';P=D/'fold_0';E=H.parent/'runtime/results'
def need(v,msg):
 if not v:raise ValueError(msg)
def parse(p):
 t={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return t,start
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
new,ns=parse(P/'candidate.tm');legacy,ls=parse(E/'candidate.legacy.tm');mp={int(q):z for q,z in json.loads((E/'legacy_mapping.json').read_text()).items()};states={q for q,b in new};need(set(mp)==states|{254}and len(set(mp.values()))==len(mp),'map not bijective');need(mp[0]==95 and mp[84]==96 and mp[254]==254,'special labels');need(ls==mp[ns],'start relabel');need(legacy=={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in new.items()},'transition relabel mismatch')
archive=H.parent/'inputs/legacy_state_map.json';original={int(k):v for k,v in json.loads(archive.read_text())['k230_to_old'].items()};original[254]=254;need(all(original.get(q)==z for q,z in mp.items()),'unregistered label relabel')
a=json.loads((D/'allocation.json').read_text());nodes=a['structures'];alloc={int(k):v for k,v in a['allocation'].items()};root=a['root'];sites=json.loads((P/'sites.json').read_text());leaves=[];branches=[];visited=set()
def walk(n,p):
 need(n not in visited,'cyclic source DAG');visited.add(n)
 node=nodes[n];need(len(node)==2,'node arity')
 if isinstance(node[0],str):
  op,arg=node;need(op in('CI','CD','CB','CC','CH'),'bad opcode');need(isinstance(arg,int) or (op=='CH' and arg is None),'bad argument');leaves.append([p,op,arg])
 else:
  need(n in alloc,'missing allocation');branches.append((n,p));walk(node[0],p+'0');walk(node[1],p+'1')
 visited.remove(n)
walk(root,'');need(leaves==sites,'source DAG leaves differ from exact source');need(alloc[root]==84,'wrong dispatcher');need(len(sites)==4799 and sum(2 if op=='CD' else 1 for pc,op,arg in sites)==6238,'wrong source case coverage')
phi=lambda q:180 if q==18 else q
hist=Counter();macros=0;literal=0;maxsteps=0
for n,pc in branches:
 for b,child in enumerate(nodes[n]):
  if isinstance(nodes[child][0],str):continue
  # All prefix bits and the left delimiter are fixed; every other tape cell
  # remains arbitrary. Acceptance is before reading the unknown next cell.
  tape={j-len(pc):int(bit)for j,bit in enumerate(pc)};tape[-len(pc)-1]=1;tape[0]=b;before=tape.copy();q=phi(alloc[n]);head=0
  for steps in range(1,66):
   need(head in tape,f'decoder reads arbitrary cell at {pc}/{b}');w,d,q=new[q,tape[head]];tape[head]=w;head+=d;literal+=1
   if head==1 and q==phi(alloc[child])and tape==before:break
  else:raise ValueError(f'decoder macro failed at {pc}/{b}')
  macros+=1;hist[steps]+=1;maxsteps=max(maxsteps,steps)
# Check source leaves form a full prefix code, independently of DAG expansion.
paths=[x[0]for x in sites];need(len(paths)==len(set(paths)),'duplicate source address');prefixes={p[:j]for p in paths for j in range(len(p))};need(not(set(paths)&prefixes),'non-prefix-free source');need(all(p+'0'in prefixes or p+'0'in paths for p in prefixes)and all(p+'1'in prefixes or p+'1'in paths for p in prefixes),'nonexhaustive source tree')
proof=json.loads((E/'proof.json').read_text());need(proof['table_sha256']==sha(P/'candidate.tm')and proof['legacy_table_sha256']==sha(E/'candidate.legacy.tm')and proof['source_sha256']==sha(P/'sites.json'),'runtime job binding mismatch');need(proof['physical_map']==[6,2,0,4,3,7,8,5,1],'wrong physical register map')
r=dict(status='PASS_INDEPENDENT_EXACT_DECODER_AND_LABEL_BINDINGS',working_states=len(states),binary_transition_rows=len(new),start_native=ns,start_legacy=ls,dispatcher_native=84,dispatcher_legacy=96,halt=254,native_max_working_label=max(states),label_map_bijection=True,label_map_matches_archived_map=True,source_leaf_occurrences=len(sites),source_guard_cases=6238,source_internal_occurrences=len(branches),allocated_source_dag_nodes=len(alloc),checked_decoder_macros=macros,decoder_macro_length_histogram=dict(hist),decoder_literal_steps=literal,maximum_decoder_macro=maxsteps,source_maximum_depth=max(map(len,paths)),source_exact_full_prefix_code=True,table_sha256=sha(P/'candidate.tm'),legacy_table_sha256=sha(E/'candidate.legacy.tm'),label_map_sha256=sha(E/'legacy_mapping.json'),archived_label_map_sha256=sha(archive),source_sha256=sha(P/'sites.json'),allocation_sha256=sha(D/'allocation.json'),checker_sha256=sha(Path(__file__)),runtime_job_status_at_audit=proof['status'],runtime_cases_at_audit=proof.get('cases'),scope='All 4,797 non-leaf decoder edges restore the entire known source prefix and delimiter while consuming exactly one source bit; no arbitrary exterior bit is read. All non-leaf occurrences are checked, not one representative per DAG node. Primitive leaf semantics and bootstrap/runtime are separate checks in the bound engine job.')
(H/'decoder_bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
