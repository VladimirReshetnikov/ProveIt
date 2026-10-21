"""Owned exact drain-loop recognition and affine matrix contraction.
Finite structural/algebraic verification, not a proof-assistant certification.
"""
if not __debug__:
 raise SystemExit("Verification requires assertions: do not use -O or PYTHONOPTIMIZE.")
import json,collections,random,hashlib
from pathlib import Path
B=Path(__file__).resolve().parent;raw=(B/'input_graph.json').read_bytes();G={int(k):v for k,v in json.loads(raw).items()};N=9

def eye():return [[int(i==j) for j in range(N+1)] for i in range(N+1)]
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(N+1)) for j in range(N+1)] for i in range(N+1)]
def add(incs):
 A=eye()
 for r,k in incs:A[r][N]+=k
 return A
def evaluate(A,R):return [sum(a*x for a,x in zip(row,R+[1])) for row in A[:-1]]
# Reject malformed graph labels and ambiguous duplicate increment entries.
for v,x in G.items():
 op=x['op']
 if not (op==['halt'] or (len(op)==2 and op[0]=='decnz' and type(op[1])==int and 0<=op[1]<N)):
  raise ValueError('Malformed operation label')
 for target,incs in x['successors']:
  seen=set()
  for r,k in incs:
   if not (type(r)==int and 0<=r<N and type(k)==int and k>=0 and r not in seen):
    raise ValueError('Malformed or duplicate increment entry')
   seen.add(r)
D={}
for v,x in G.items():
 if x['op'][0]!='decnz':continue
 r=x['op'][1];(n,inc),(z,iz)=x['successors']
 if n==v and dict(inc).get(r,0)==0:
  assert z!=v
  A=eye();A[r]=[0]*(N+1)
  for j,k in inc:A[j][r]+=k
  for j,k in iz:A[j][N]+=k
  D[v]={'register':r,'increments':inc,'exit_increments':iz,'target':z,'matrix':A}
K=set(G)-set(D)
def path(start,incs):
 A=add(incs);v=start;seen=set();trace=[]
 while v in D:
  assert v not in seen,('deterministic drain cycle',start,v)
  seen.add(v);trace.append(v);A=mul(D[v]['matrix'],A);v=D[v]['target']
 return {'target':v,'matrix':A,'drain_path':trace}
H={}
for v in sorted(K):
 x=G[v];H[v]={'op':x['op'],'successors':[path(t,incs) for t,incs in x['successors']]}
entry=path(0,[])
# Independent semantic regression: run original test graph, not matrix updates.
def concrete_step(v,R):
 x=G[v];r=x['op'][1];R=R.copy();nz=R[r]>0
 if nz:R[r]-=1
 t,incs=x['successors'][0 if nz else 1]
 for j,k in incs:R[j]+=k
 return t,R
rnd=random.Random(215);local_cases=0
for v,d in D.items():
 for z in range(5):
  R=[rnd.randrange(6) for _ in range(N)];R[d['register']]=z
  w,Q=concrete_step(v,R)
  for _ in range(z):
   if w!=v:break
   w,Q=concrete_step(w,Q)
  assert w==d['target'] and Q==evaluate(d['matrix'],R)
  local_cases+=1
# Algebraic verifier checks emitted edge matrices by applying each emitted drain
# to all symbolic affine coordinates, independently of matrix multiplication.
def symbolic(incs,trace):
 cols=add(incs)
 for v in trace:
  d=D[v];r=d['register'];old=cols[r].copy();cols[r]=[0]*(N+1)
  for j,k in d['increments']:
   cols[j]=[x+k*y for x,y in zip(cols[j],old)]
  for j,k in d['exit_increments']:cols[j][N]+=k
 return cols
for v,x in H.items():
 for b,e in enumerate(x['successors']):
  target,incs=G[v]['successors'][b];cursor=target
  for d in e['drain_path']:
   assert cursor==d;cursor=D[d]['target']
  assert cursor==e['target'] and cursor in K
  assert symbolic(incs,e['drain_path'])==e['matrix']
assert symbolic([],entry['drain_path'])==entry['matrix']
traces=[e['drain_path'] for x in H.values() for e in x['successors']]
shapes=collections.Counter((d['register'],tuple(map(tuple,d['increments'])),tuple(map(tuple,d['exit_increments']))) for d in D.values())
used={d for t in traces+[entry['drain_path']] for d in t};assert used==set(D)
res={'input_sha256':hashlib.sha256(raw).hexdigest(),'input_vertices':len(G),'drain_vertices':len(D),'remaining_vertices':len(H),'remaining_tests':sum(x['op'][0]=='decnz' for x in H.values()),'remaining_halts':sum(x['op'][0]=='halt' for x in H.values()),'contracted_edges':sum(len(x['successors']) for x in H.values()),'distinct_drain_shapes':len(shapes),'max_drain_chain':max(map(len,traces)), 'summed_edge_drain_references':sum(map(len,traces)), 'all_drains_covered':used==set(D),'local_concrete_regressions':local_cases,'symbolic_matrix_verification':True,'entry':entry,'maximum_matrix_coefficient':max(c for x in H.values() for e in x['successors'] for row in e['matrix'] for c in row),'verification':'Finite Python structural/algebraic checks. Generic drain semantics not kernel-compiled here.'}
(B/'DRAIN_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n');(B/'drain_certificates.json').write_text(json.dumps(D));(B/'affine_graph.json').write_text(json.dumps(H));print(json.dumps({k:v for k,v in res.items() if k!='entry'},indent=2))
# Compact proof data: shared affine matrices and a rank for every eliminated loop.
mids={};matrix_table=[];compact={}
for v,x in H.items():
 edges=[]
 for e in x['successors']:
  key=tuple(map(tuple,e['matrix']))
  if key not in mids:mids[key]=len(matrix_table);matrix_table.append(e['matrix'])
  edges.append([e['target'],mids[key]])
 compact[v]={'op':x['op'],'successors':edges}
ranks={}
def rank(v):
 if v not in D:return 0
 if v not in ranks:ranks[v]=1+rank(D[v]['target'])
 return ranks[v]
for v in D:rank(v)
assert max(ranks.values())<=6
for v,d in D.items():assert ranks[v]>rank(d['target'])
for v,x in compact.items():
 for compact_edge,expanded in zip(x['successors'],H[v]['successors']):
  t,i=compact_edge;assert t==expanded['target'] and matrix_table[i]==expanded['matrix']
artifact={'registers':9,'nonzero_update':'decrement_before_affine','matrix_convention':'10x10 homogeneous, column vector R0..R8,1; apply after decrement on nonzero branch','entry':entry,'matrices':matrix_table,'nodes':compact}
(B/'compact_affine_graph.json').write_text(json.dumps(artifact,separators=(',',':'))+'\n');(B/'drain_ranks.json').write_text(json.dumps(ranks))
res.update({'distinct_affine_matrices':len(matrix_table),'max_drain_rank':max(ranks.values()),'compact_affine_bytes':(B/'compact_affine_graph.json').stat().st_size,'compact_roundtrip_checked':True})
(B/'DRAIN_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
