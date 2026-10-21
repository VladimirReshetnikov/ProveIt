"""Independent owned artifact validator and adversarial semantic regression tests.
No repository scripts are imported; no theorem-prover certification is claimed.
"""
if not __debug__:
 raise SystemExit("Verification requires assertions: do not use -O or PYTHONOPTIMIZE.")
import copy,json
from pathlib import Path
B=Path(__file__).resolve().parent
N=9
CONVENTION='10x10 homogeneous, column vector R0..R8,1; apply after decrement on nonzero branch'
def require(p,msg):
 if not p:raise ValueError(msg)
def ident():return [[int(i==j) for j in range(N+1)] for i in range(N+1)]
def counts(xs):
 a=[0]*N
 for r,k in xs:
  require(type(r)==int and 0<=r<N and type(k)==int and k>=0,'bad increment')
  a[r]+=k
 return a
def sym_add(a):
 rows=ident()
 for j,k in enumerate(a):rows[j][-1]=k
 return rows
def sym_drain(rows,r,c,d):
 old=rows[r][:];out=[row[:] for row in rows];out[r]=[0]*(N+1)
 for j in range(N):
  if j!=r:out[j]=[x+c[j]*y for x,y in zip(out[j],old)]
  out[j][-1]+=d[j]
 return out
def ev(M,R):return [sum(x*y for x,y in zip(row,R+[1])) for row in M[:-1]]
def validate(G,D,ranks,C):
 require(C['registers']==N,'register count')
 require(C['nonzero_update']=='decrement_before_affine','nonzero semantic contract')
 require(C['matrix_convention']==CONVENTION,'matrix convention')
 K=set(G)-set(D)
 require(set(C['nodes'])==K,'core partition')
 require(set(ranks)==set(D),'rank domain')
 for v,x in G.items():
  op=x['op']
  require(op==['halt'] or (len(op)==2 and op[0]=='decnz' and type(op[1])==int and 0<=op[1]<N),'node kind or register range')
  require(len(x['successors'])==(2 if x['op'][0]=='decnz' else 0),'arity')
  for t,incs in x['successors']:
   require(str(t) in G,'target outside graph');counts(incs)
 for v,d in D.items():
  x=G[v];r=d['register']
  require(x['op']==['decnz',r],'removed test label')
  (nz,c0),(z,d0)=x['successors'];c=counts(c0);a=counts(d0)
  require(str(nz)==v and c[r]==0 and str(z)!=v,'drain shape')
  require(d['increments']==c0 and d['exit_increments']==d0 and d['target']==z,'local certificate binding')
  require(d['matrix']==sym_drain(ident(),r,c,a),'local matrix')
  require(type(ranks[v])==int and ranks[v]>0,'natural positive rank')
  require(ranks[v]>ranks.get(str(z),0),'strict exit rank')
 for M in C['matrices']:
  require(len(M)==N+1 and all(len(row)==N+1 for row in M),'matrix dimensions')
  require(all(type(k)==int and k>=0 for row in M for k in row),'matrix naturals')
  require(M[-1]==ident()[-1],'homogeneous row')
 def follow(t,a):
  rows=sym_add(a);seen=set();path=[]
  while str(t) in D:
   v=str(t);require(v not in seen,'exit cycle');seen.add(v);path.append(t)
   d=D[v];rows=sym_drain(rows,d['register'],counts(d['increments']),counts(d['exit_increments']));t=d['target']
  require(str(t) in K,'terminal core')
  return t,rows,path
 for v,x in C['nodes'].items():
  require(x['op']==G[v]['op'],'retained label')
  require(len(x['successors'])==len(G[v]['successors']),'core arity')
  for (t,incs),(q,m) in zip(G[v]['successors'],x['successors']):
   require(type(m)==int and 0<=m<len(C['matrices']),'matrix index')
   dest,M,_=follow(t,counts(incs))
   require(q==dest and C['matrices'][m]==M,'edge product or target')
 t,M,path=follow(0,[0]*N)
 require(C['entry']=={'target':t,'matrix':M,'drain_path':path},'entry normalization')
 return True

def step(G,v,R):
 r=G[str(v)]['op'][1];Q=R[:];nz=Q[r]>0
 if nz:Q[r]-=1
 t,incs=G[str(v)]['successors'][0 if nz else 1]
 for j,k in incs:Q[j]+=k
 return t,Q
def core_step(C,v,R,forget_decrement=False):
 r=C['nodes'][str(v)]['op'][1];Q=R[:];nz=Q[r]>0
 if nz and not forget_decrement:Q[r]-=1
 t,m=C['nodes'][str(v)]['successors'][0 if nz else 1]
 return t,ev(C['matrices'][m],Q)
G=json.loads((B/'input_graph.json').read_text());D=json.loads((B/'drain_certificates.json').read_text());ranks=json.loads((B/'drain_ranks.json').read_text());C=json.loads((B/'compact_affine_graph.json').read_text())
assert validate(G,D,ranks,C)
results=[]
def rejects(name,g=G,d=D,r=ranks,c=C):
 try:validate(g,d,r,c)
 except ValueError as ex:results.append({'mutation':name,'rejected':True,'reason':str(ex)});return
 raise AssertionError('Accepted adversarial mutation: '+name)
v=next(iter(D));r=D[v]['register'];g=copy.deepcopy(G);g[v]['successors'][0][1].append([r,1]);rejects('self-loop increments tested register',g=g)
g=copy.deepcopy(G);g[v]['successors'][0][1].extend([[r,1],[r,0]]);rejects('duplicate tested-register entries cannot hide self increment',g=g)
g=copy.deepcopy(G);g[v]['successors'][0][1].append([r,-1]);rejects('negative increment',g=g)
g=copy.deepcopy(G);g[v]['successors'][0][1].append([N,1]);rejects('out-of-range increment register',g=g)
g=copy.deepcopy(G);g['0']['op'][1]=N;rejects('out-of-range retained test register',g=g)
rk=copy.deepcopy(ranks);rk[v]=ranks.get(str(D[v]['target']),0);rejects('nondecreasing exit rank',r=rk)
c=copy.deepcopy(C);c['nonzero_update']='affine_without_decrement';rejects('missed core decrement semantic contract',c=c)
c=copy.deepcopy(C);c['entry']['matrix'][0][-1]+=1;rejects('wrong entry transform',c=c)
# Mutate a real noncommuting product. Construct reverse application order by
# symbolic substitutions, rather than using the generator matrix multiplier.
found=False
for v,x in C['nodes'].items():
 for b,(t,incs) in enumerate(G[v]['successors']):
  path=[]
  while str(t) in D:path.append(str(t));t=D[str(t)]['target']
  rows=ident()
  for w in reversed(path):
   d=D[w];rows=sym_drain(rows,d['register'],counts(d['increments']),counts(d['exit_increments']))
  for j,k in enumerate(counts(incs)):rows[j][-1]+=k
  mid=x['successors'][b][1]
  if rows!=C['matrices'][mid]:
   c=copy.deepcopy(C);c['matrices'].append(rows);c['nodes'][v]['successors'][b][1]=len(c['matrices'])-1
   rejects('reversed affine composition order',c=c);found=True;break
 if found:break
assert found
# End-to-end edge regressions explicitly include the retained decrement.
cases=0;witness=None
for v,x in C['nodes'].items():
 if x['op'][0]=='halt':continue
 for amount in (0,1,3):
  R=[2]*N;R[x['op'][1]]=amount;t,Q=step(G,int(v),R);steps=1
  while str(t) in D:
   t,Q=step(G,t,Q);steps+=1
   assert steps<100000
  assert (t,Q)==core_step(C,int(v),R);cases+=1
  if amount and witness is None and core_step(C,int(v),R,True)!=(t,Q):
   witness={'vertex':int(v),'registers':R,'correct_target_and_registers':[t,Q],'without_decrement':core_step(C,int(v),R,True)}
assert witness is not None
out={'independent_validator_accepts':True,'adversarial_mutations':results,'full_core_edge_regressions':cases,'missed_decrement_counterexample':witness,'initial_vertex_is_core': '0' in C['nodes'],'initial_matrix_is_identity':C['entry']['matrix']==ident(),'status':'Owned finite structural checks and concrete regressions; not kernel certification.'}
(B/'ADVERSARIAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
