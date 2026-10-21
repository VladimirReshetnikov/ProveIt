"""Owned labelled bisimulation quotient; no repository code imported."""
if not __debug__:
 raise SystemExit("Verification requires assertions: do not use -O or PYTHONOPTIMIZE.")
from pathlib import Path
import json,collections,hashlib
B=Path(__file__).resolve().parent
raw=(B/'input_graph.json').read_bytes();G={int(k):v for k,v in json.loads(raw).items()}
def partition(signatures):
 d={};out={}
 for v in sorted(signatures):
  s=signatures[v]
  if s not in d:d[s]=len(d)
  out[v]=d[s]
 return out
P=partition({v:tuple(x['op']) for v,x in G.items()});rounds=[len(set(P.values()))]
while True:
 Q=partition({v:(tuple(x['op']),tuple((P[t],tuple(map(tuple,incs))) for t,incs in x['successors'])) for v,x in G.items()})
 rounds.append(len(set(Q.values())))
 if Q==P:break
 P=Q
blocks=collections.defaultdict(list)
for v,c in P.items():blocks[c].append(v)
# Explicit validation of the returned homomorphism, independent of convergence.
H={}
for c,vs in blocks.items():
 sigs=[(G[v]['op'],[(P[t],incs) for t,incs in G[v]['successors']]) for v in vs]
 assert all(x==sigs[0] for x in sigs)
 H[c]={'op':sigs[0][0],'successors':sigs[0][1]}
seen={0};todo=[0]
while todo:
 v=todo.pop()
 for t,_ in G[v]['successors']:
  if t not in seen:seen.add(t);todo.append(t)
res={'input_sha256':hashlib.sha256(raw).hexdigest(),'input_vertices':len(G),'reachable_ignoring_register_guards':len(seen),'quotient_vertices':len(H),'partition_refinement_sizes':rounds,'class_size_histogram':dict(collections.Counter(map(len,blocks.values()))),'largest_classes':sorted(blocks.values(),key=len,reverse=True)[:10],'homomorphism_full_check':True,'interpretation':'Ordinary finite data audit, not proof assistant verification.'}
(B/'QUOTIENT_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n');(B/'quotient_graph.json').write_text(json.dumps(H));(B/'quotient_map.json').write_text(json.dumps(P));print(json.dumps(res,indent=2))
