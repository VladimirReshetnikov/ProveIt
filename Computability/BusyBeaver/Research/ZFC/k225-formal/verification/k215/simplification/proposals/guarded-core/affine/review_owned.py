"""Owned read-only-data audit. Never imports or executes packet programs.
Ordinary Python finite checks, not Lean/Rocq validation.
"""
from pathlib import Path
import collections, hashlib, itertools, json, os, re, sys
if not __debug__ or 'PYTHONOPTIMIZE' in os.environ:
 raise SystemExit('Assertions must be enabled and PYTHONOPTIMIZE must be absent')
sys.setrecursionlimit(30000)
HERE=Path(__file__).resolve().parent
P=HERE/'extracted/Affine_Proof_Cores_and_Transport_2026-10-21'
def load(p): return json.loads(p.read_text())
def gh(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def out(name,x): (HERE/name).write_text(json.dumps(x,indent=2)+'\n')
# Bind every received payload, not its claims of execution.
manifest=load(P/'MANIFEST.json')
for f,m in manifest.items():
 b=(P/f).read_bytes();assert len(b)==m['bytes'] and hashlib.sha256(b).hexdigest()==m['sha256'],f
for pin in load(P/'graph_origin/SOURCE_PINS.json')['sources']:
 b=(P/'graph_origin/upstream'/pin['name']).read_bytes();assert gh(b)==pin['git_blob_sha']
for pin in load(HERE/'CURRENT_SOURCE_PINS.json'):
 b=(HERE/'current_sources'/Path(pin['path']).name).read_bytes();assert gh(b)==pin['git_blob_sha']
# Build a new tree parser with a complete token-consumption check.
def tree_literal(s,name):
 text=s.split('def '+name+' : Tree :=',1)[1].split('\n\n',1)[0]
 tokens=re.findall(r'\.[a-zA-Z]+|[0-9]+|[()]',text)
 it=iter(tokens); consumed=0
 def take():
  nonlocal consumed
  consumed+=1;return next(it)
 def parse():
  tag=take()
  if tag=='(':
   val=parse();assert take()==')';return val
  if tag=='.node': return ('N',parse(),parse())
  if tag=='.leaf': return ('L',parse())
  if tag=='.halt': return ('halt',)
  assert tag in ('.inc','.decnz','.brk','.cont'),tag
  n=take();assert n.isdigit();return (tag[1:],int(n))
 t=parse();assert consumed==len(tokens);return t
src=(P/'graph_origin/upstream/KSource215Data.lean').read_text()
phase5_pin=load(HERE/'CURRENT_PHASE5_SOURCE_PIN.json')
assert phase5_pin['commit']=='0359ebda60aaf52758358e1450a04988136db67e'
assert phase5_pin['git_blob_sha']=='c966e0626e98d038d8b4e9300d37414e2ea128ed'
assert phase5_pin['sha256']=='ccf9e2970482a772bea93919974431c39c442a6c23f83731c0b561c9945fae1e'
assert phase5_pin['local']=='current_sources/KSource215Data.phase5.lean'
curpath=HERE/phase5_pin['local'];current_bytes=curpath.read_bytes()
assert len(current_bytes)==phase5_pin['bytes']==432131
assert gh(current_bytes)==phase5_pin['git_blob_sha']
assert hashlib.sha256(current_bytes).hexdigest()==phase5_pin['sha256']
current_trees_equal=all(tree_literal(src,n)==tree_literal(current_bytes.decode('utf-8'),n) for n in ('t215','tD'))
assert current_trees_equal

def enum_leaves(t):
 ans=[];stack=[(t,())]
 while stack:
  node,path=stack.pop()
  if node[0]=='L':ans.append((path,node[1]))
  else:stack.extend(((node[2],path+(1,)),(node[1],path+(0,))))
 return ans

def canonical_graph(t):
 leaves=enum_leaves(t);ordinals={p:i for i,(p,e) in enumerate(leaves)}
 def lookup(path):
  node=t;q=[]
  while node[0]=='N':
   b=path[len(q)] if len(q)<len(path) else 0
   q.append(b);node=node[1+b]
  return tuple(q),node[1]
 def increment(path):
  width=len(path);num=sum(b<<(width-i-1) for i,b in enumerate(path))
  nxt=(num+1)%(1<<width)
  return tuple((nxt>>(width-i-1))&1 for i in range(width))
 def strip(path,b,n):
  k=len(path)
  while n and k:
   k-=1;n-=path[k]==b
  return path[:k]
 def segment(path):
  adds=[0]*9;seen=set();steps=0
  while True:
   q,op=lookup(path)
   if op[0] in ('decnz','halt'):return [ordinals[q],[[i,n] for i,n in enumerate(adds) if n]],steps
   assert q not in seen;seen.add(q);steps+=1
   if op[0]=='inc':adds[op[1]]+=1;path=increment(q)
   elif op[0]=='brk':path=increment(strip(q,0,op[1]))
   else:assert op[0]=='cont';path=strip(q,1,op[1])
 ans={};lens=[]
 for v,(q,op) in enumerate(leaves):
  if op[0]=='halt':ans[v]={'op':list(op),'successors':[]}
  elif op[0]=='decnz':
   nz,k=segment(increment(q));z,j=segment(increment(strip(q,0,1)));lens.extend((k,j))
   ans[v]={'op':list(op),'successors':[nz,z]}
 return ans,segment(())[0],len(leaves),max(lens),sum(lens)
G,entry,leaves,mx,tot=canonical_graph(tree_literal(src,'t215'))
G2,entry2,leaves2,mx2,tot2=canonical_graph(tree_literal(src,'tD'))
assert G==G2 and entry==entry2==[0,[]] and leaves==leaves2==4751
assert G=={int(k):v for k,v in load(P/'structural/input_graph.json').items()}
A={int(k):v for k,v in load(P/'structural/affine_graph.json').items()}
D={int(k):v for k,v in load(P/'structural/drain_certificates.json').items()}
rank={int(k):v for k,v in load(P/'structural/drain_ranks.json').items()}
I=[[int(i==j) for j in range(10)] for i in range(10)]
def vec(xs):
 y=[0]*9
 for r,n in xs:assert type(r)==int and 0<=r<9 and type(n)==int and n>=0;y[r]+=n
 return y
for v,n in G.items():
 assert n['op']==['halt'] or (n['op'][0]=='decnz' and 0<=n['op'][1]<9)
 for dst,x in n['successors']:assert dst in G;vec(x)
# Exact local drain recognition, independent of received certificate partition.
recognized={}
for v,n in G.items():
 if n['op'][0]=='halt':continue
 r=n['op'][1];(a,c),(b,d)=n['successors'];c=vec(c);d=vec(d)
 if a==v and b!=v and c[r]==0:recognized[v]=(r,c,b,d)
assert set(D)==set(recognized) and set(A)==set(G)-set(D)
def combine(M,N):return [[sum(M[i][k]*N[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
def evalM(M,R):return [sum(a*b for a,b in zip(row,R+[1])) for row in M[:9]]
for v,(r,c,b,d) in recognized.items():
 M=[row[:] for row in I];M[r]=[0]*10
 for j in range(9):
  if j!=r:M[j][r]+=c[j]
  M[j][9]=d[j]
 cert=D[v];assert cert['register']==r and vec(cert['increments'])==c and cert['target']==b and vec(cert['exit_increments'])==d and cert['matrix']==M
 assert type(rank[v])==int and rank[v]>0
 if b in D:assert rank[b]<rank[v]

def drain_chain(dst,M):
 path=[]
 while dst in D:
  assert dst not in path;path.append(dst)
  M=combine(D[dst]['matrix'],M);dst=D[dst]['target']
 return dst,M,path
for v,n in A.items():
 assert n['op']==G[v]['op'] and len(n['successors'])==len(G[v]['successors'])
 for (dst,x),edge in zip(G[v]['successors'],n['successors']):
  M=[row[:] for row in I]
  for r,nr in enumerate(vec(x)):M[r][9]=nr
  target,product,path=drain_chain(dst,M)
  assert edge=={'target':target,'matrix':product,'drain_path':path}
C=load(P/'structural/compact_affine_graph.json')
assert C['nonzero_update']=='decrement_before_affine'
assert len(C['matrices'])==33 and len(A)==367
assert C['entry']=={'target':0,'matrix':I,'drain_path':[]}
assert set(map(int,C['nodes']))==set(A)
for key,n in C['nodes'].items():
 original=A[int(key)]
 assert n['op']==original['op'] and len(n['successors'])==len(original['successors'])
 for (dst,mi),edge in zip(n['successors'],original['successors']):
  assert 0<=mi<len(C['matrices']) and dst==edge['target'] and C['matrices'][mi]==edge['matrix']
# Second-layer total-loop recognition with full 9-register maps.
tri=[row[:] for row in I];tri[1]=[0]*10;tri[6][1]=1;tri[7][1]=1;tri[7][6]=1;tri[7][9]=1
clear=[row[:] for row in I];clear[5]=[0]*10
loops={}
for v,n in A.items():
 if n['op']==['decnz',6] and n['successors'][0]['target']==v:
  M=n['successors'][0]['matrix']
  assert M in (tri,clear)
  loops[v]='triangular' if M==tri else 'clear'
assert collections.Counter(loops.values())=={'triangular':174,'clear':4}
retained=set(A)-set(loops);assert 0 in retained
ranks={}
def rank2(v,seen=()):
 if v not in loops:return 0
 if v in ranks:return ranks[v]
 assert v not in seen,'cyclic total-loop exits'
 ranks[v]=1+rank2(A[v]['successors'][1]['target'],seen+(v,));return ranks[v]
for v in loops:rank2(v)
assert max(ranks.values())==7
# No natural subtraction before a proven positive branch.
def graph_step(g,v,R,affine=False):
 n=g[v];assert n['op'][0]=='decnz';r=n['op'][1];b=0 if R[r]>0 else 1
 Q=R[:]
 if b==0:Q[r]-=1
 if affine:
  e=n['successors'][b];return e['target'],evalM(e['matrix'],Q)
 dst,x=n['successors'][b];return dst,[q+a for q,a in zip(Q,vec(x))]

def summary(v,R):
 Q=R[:];n,a=R[6],R[1]
 if n>0:
  Q[6]=0
  if loops[v]=='triangular':Q[1]=0;Q[7]+= (n+a)*(n+a+1)//2
  else:Q[5]=0
 edge=A[v]['successors'][1]
 return edge['target'],evalM(edge['matrix'],Q)

def literal_to_exit(g,v,R,affine):
 entry=v;steps=0
 while True:
  v,R=graph_step(g,v,R,affine);steps+=1
  if v not in D and v!=entry:return (v,R),steps
  assert steps<200000,'finite regression bound exceeded'
# Check all 178 actual occurrence bindings, all zero/positive counter combinations,
# arbitrary auxiliary scratch values, and all nine output coordinates.
local=0;raw_steps=0
for v in loops:
 for n,a,z in itertools.product(range(7),range(7),range(3)):
  R=[3, a, 2, 1, 2, 4, n, z, 2]
  expected=summary(v,R)
  direct,steps=literal_to_exit(G,v,R,False)
  affine,ct=literal_to_exit(A,v,R,True)
  assert expected==direct==affine,(v,R,expected,direct)
  want=(n+a if n>0 and loops[v]=='triangular' else n)+1
  assert ct==want,(v,R,ct,want)
  local+=1;raw_steps+=steps
# Structural contraction as expression circuits, not expanded high-degree polynomials.
macro_nodes={};chain_refs=0;max_chain=0
for v in sorted(retained):
 n=A[v];eds=[]
 for edge in n['successors']:
  dst=edge['target'];path=[]
  while dst in loops:
   assert dst not in path;path.append(dst);dst=A[dst]['successors'][1]['target']
  eds.append({'target':dst,'initial_affine':edge['matrix'],'total_loop_path':path})
  chain_refs+=len(path);max_chain=max(max_chain,len(path))
 macro_nodes[v]={'op':n['op'],'successors':eds}
assert len(macro_nodes)==189 and sum(len(n['successors']) for n in macro_nodes.values())==376
assert sum(n['op']==['halt'] for n in macro_nodes.values())==1
assert {u for n in macro_nodes.values() for e in n['successors'] for u in e['total_loop_path']}==set(loops)
# Explicit counterexamples to collapsing the zero case or missing core decrement.
wrong_zero=next(v for v,k in loops.items() if k=='triangular')
R=[0,2,0,0,0,0,0,0,0]
Q=R[:];Q[1]=0;Q[7]=3
assert evalM(A[wrong_zero]['successors'][1]['matrix'],Q)!=summary(wrong_zero,R)[1]
clear_node=next(v for v,k in loops.items() if k=='clear');Rclear=[0,0,0,0,0,5,0,0,0]
Qclear=Rclear[:];Qclear[5]=0
clear_zero_counterexamples=[]
for v,k in loops.items():
 if k=='clear':
  correct=summary(v,Rclear);wrong=(A[v]['successors'][1]['target'],evalM(A[v]['successors'][1]['matrix'],Qclear))
  assert correct!=wrong
  clear_zero_counterexamples.append({'node':v,'input':Rclear,'correct':correct,'wrong_unconditional_clear':wrong})
loop_definitions={v:{'kind':kind,'zero_exit':A[v]['successors'][1]} for v,kind in loops.items()}
source_bindings={f:hashlib.sha256((P/f).read_bytes()).hexdigest() for f in ('structural/input_graph.json','structural/affine_graph.json')}
out('GUARDED_CORE.json',{'semantics':'decrement before initial affine; then each guarded total-loop summary INCLUDING its zero exit affine', 'loop_contracts':{'triangular':'If R6=0, preserve all registers before zero_exit. If R6>0, simultaneously set R1=R6=0, add (old R1+old R6)*(old R1+old R6+1)/2 to R7, preserve all other registers; then apply zero_exit matrix.', 'clear':'If R6=0, preserve all registers before zero_exit. If R6>0, set R5=R6=0 and preserve all other registers; then apply zero_exit matrix.'},'source_sha256':source_bindings,'entry':0,'halt':[v for v in retained if A[v]['op']==['halt']],'nodes':macro_nodes,'loop_kinds':loops,'loop_definitions':loop_definitions,'derived_exit_ranks':ranks})
out('CLEAR_ZERO_COUNTEREXAMPLES.json',clear_zero_counterexamples)
# The verbose core is the review format. Reuse the incoming 33-matrix dictionary
# for a smaller exact serialization, without claiming kernel or runtime savings.
full=load(HERE/'GUARDED_CORE.json');small=json.loads(json.dumps(full))
small['matrices']=C['matrices']
def matrix_id(M):return C['matrices'].index(M)
for node in small['nodes'].values():
 for edge in node['successors']:edge['initial_affine']=matrix_id(edge['initial_affine'])
for definition in small['loop_definitions'].values():
 definition['zero_exit']['matrix']=matrix_id(definition['zero_exit']['matrix'])
expanded=json.loads(json.dumps(small));matrices=expanded.pop('matrices')
for node in expanded['nodes'].values():
 for edge in node['successors']:edge['initial_affine']=matrices[edge['initial_affine']]
for definition in expanded['loop_definitions'].values():
 definition['zero_exit']['matrix']=matrices[definition['zero_exit']['matrix']]
assert expanded==full
(HERE/'GUARDED_CORE_COMPACT.json').write_text(json.dumps(small,separators=(',',':'))+'\n')
out('OWN_AUDIT.json',{'status':'PASS: owned finite checks only; no received programs executed, no Lean/Rocq build','manifest_files':len(manifest),'source_git_pins_checked':4,'current_phase5_tree_literals_equal':current_trees_equal,'canonical_graph_vertices':len(G),'canonical_edges':2850,'leaves_each':leaves,'max_segment':mx,'sum_segment':tot,'drain_nodes':len(D),'affine_core_vertices':len(A),'affine_matrices':33,'new_triangular_macros':174,'new_clear_macros':4,'guarded_core_vertices':len(macro_nodes),'guarded_core_tests':188,'guarded_core_halts':1,'guarded_core_edges':376,'max_new_exit_rank':max(ranks.values()),'macro_chain_references':chain_refs,'max_macro_edge_chain':max_chain,'actual_occurrence_regressions':local,'original_graph_transitions_replayed':raw_steps,'all_nine_registers_compared':True,'outer_affine_step_counts_checked':True,'zero_case_counterexample':{'node':wrong_zero,'registers':[0,2,0,0,0,0,0,0,0],'correct':summary(wrong_zero,[0,2,0,0,0,0,0,0,0]),'wrong_if_positive_formula_applied':(A[wrong_zero]['successors'][1]['target'],evalM(A[wrong_zero]['successors'][1]['matrix'],Q))}})
print((HERE/'OWN_AUDIT.json').read_text())
