#!/usr/bin/env python3
from pathlib import Path
from collections import deque
import hashlib,json
H=Path(__file__).resolve().parent;D=H.parent/'canonical';N=H.parent/'fold_binding/fold_0'
def need(b,m):
 if not b:raise ValueError(m)
def table(p):
 t={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in t,'duplicate row');need(b in(0,1)and w in(0,1)and d in('L','R'),'bad binary row');t[q,b]=(w,d,z)
 qs={q for q,b in t};need(set(t)=={(q,b)for q in qs for b in(0,1)},'not total');return t,start,qs
native,ns,nq=table(N/'candidate.tm');canon,cs,cq=table(D/'k223.tm');record=json.loads((D/'canonicalization.json').read_text());halt=record['halt'];to={int(k):v for k,v in record['native_to_canonical'].items()};fr={int(k):v for k,v in record['canonical_to_native'].items()}
need(nq|{254}==set(to),'forward map domain');need(set(to.values())==cq|{halt}and len(set(to.values()))==len(to),'forward bijection');need(fr=={v:k for k,v in to.items()},'inverse mismatch');need(cq==set(range(223)),'nonconsecutive canonical states');need(cs==ns==0 and to[0]==0 and to[84]==22 and to[254]==halt,'special state mismatch');need(canon=={(to[q],b):(w,d,to[z])for(q,b),(w,d,z)in native.items()},'not exact isomorphism')
# Reconstruct the BFS order independently from the native table.
order={ns:0};todo=deque([ns])
while todo:
 q=todo.popleft()
 for b in(0,1):
  z=native[q,b][2]
  if z!=254 and z not in order:order[z]=len(order);todo.append(z)
need(len(order)==223,'not all working states structurally reachable');order[254]=halt;need(order==to,'mapping does not match read-0-before-1 BFS')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();need(sha(D/'k223.tm')==record['canonical_sha256']=='7edafbb2395d39e3b0895a5e0f4da61e12a371b0af71ef4cfb1a43c06e7b917f','canonical hash mismatch');need(sha(D/'k223.native.tm')==sha(N/'candidate.tm')==record['native_sha256'],'native copy mismatch');need(sha(D/'sites223.json')==sha(N/'sites.json')==record['source_sha256'],'source copy mismatch')
r=dict(status='PASS_INDEPENDENT_223_CANONICAL_ISOMORPHISM',working_states=223,transition_rows=446,start=0,dispatcher=22,halt=halt,bfs_order_independently_reconstructed=True,all_working_states_graph_reachable=True,canonical_sha256=sha(D/'k223.tm'),native_sha256=sha(N/'candidate.tm'),source_sha256=sha(N/'sites.json'),canonicalization_record_sha256=sha(D/'canonicalization.json'),checker_sha256=sha(Path(__file__)),scope='Exact state-label bijection and all 446 transition rows, plus identical source bytes. The native proof therefore transports to the canonical table without a new simulation assumption.')
(H/'canonical_isomorphism.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
