"""Owned exact arithmetic-loop recognition, finite checks and adversarial tests.
No repository script execution; generic theorem is mathematical, not compiled.
"""
if not __debug__:
 raise SystemExit('Verification requires assertions; disable -O/PYTHONOPTIMIZE.')
import json,hashlib,copy
from pathlib import Path
B=Path(__file__).resolve().parent
raw=(B/'input_affine_graph.json').read_bytes();C=json.loads(raw);G=C['nodes'];M=C['matrices'];N=9

def need(p,msg):
 if not p:raise ValueError(msg)
def eye():return [[int(i==j) for j in range(10)] for i in range(10)]
def apply(A,R):return [sum(x*y for x,y in zip(row,R+[1])) for row in A[:-1]]
def expected(kind):
 A=eye()
 if kind=='triangular':
  A[1]=[0]*10;A[6][1]=1;A[7][1]=1;A[7][6]=1;A[7][9]=1
 elif kind=='clear_positive':A[5]=[0]*10
 else:raise ValueError('unknown arithmetic summary')
 return A

def summary(kind,R):
 Q=R[:];x,s=R[6],R[1]
 if x:
  Q[6]=0
  if kind=='triangular':Q[1]=0;Q[7]+=(x+s)*(x+s+1)//2
  elif kind=='clear_positive':Q[5]=0
  else:raise ValueError('unknown summary')
 return Q

def step(v,R):
 x=G[str(v)];Q=R[:];r=x['op'][1];b=0 if R[r]>0 else 1
 if b==0:Q[r]-=1
 t,m=x['successors'][b];return t,apply(M[m],Q)
D={}
for v,x in G.items():
 if x['op']==['decnz',6] and str(x['successors'][0][0])==v:
  for kind in ('triangular','clear_positive'):
   if M[x['successors'][0][1]]==expected(kind):
    t,m=x['successors'][1];D[v]={'kind':kind,'exit':t,'exit_matrix':m};break
K=set(G)-set(D);ranks={}
def rank(v,seen=()):
 if v not in D:return 0
 need(v not in seen,'silent summary cycle')
 if v not in ranks:ranks[v]=1+rank(str(D[v]['exit']),seen+(v,))
 return ranks[v]
for v in D:rank(v)

def path(t,m):
 code=[['affine',m]];seen=set()
 while str(t) in D:
  v=str(t);need(v not in seen,'silent summary cycle');seen.add(v)
  code.append(['summary',D[v]['kind']]);code.append(['affine',D[v]['exit_matrix']]);t=D[v]['exit']
 return [t,code]
H={v:{'op':G[v]['op'],'successors':[path(t,m) for t,m in G[v]['successors']]} for v in sorted(K,key=int)}
entry=C['entry'];need(str(entry['target']) in K and entry['matrix']==eye(),'unexpected initial normalization')
A={'registers':9,'nonzero_update':'decrement_before_program','entry':entry,'matrices':M,'nodes':H}

def validate(d,r,a):
 need(a['nonzero_update']=='decrement_before_program','core decrement contract')
 need(a['registers']==9 and a['entry']==entry and a['matrices']==M,'entry or matrix binding')
 need(set(d)==set(r) and set(a['nodes'])==set(G)-set(d),'partition')
 for v,c in d.items():
  x=G[v];need(x['op']==['decnz',6],'tested register')
  need(str(x['successors'][0][0])==v,'self loop')
  need(M[x['successors'][0][1]]==expected(c['kind']),'exact summary body')
  need(x['successors'][1]==[c['exit'],c['exit_matrix']],'exit binding')
  need(type(r[v])==int and r[v]>r.get(str(c['exit']),0),'strict rank')
 for v,x in a['nodes'].items():
  need(x['op']==G[v]['op'] and len(x['successors'])==len(G[v]['successors']),'retained label')
  for (t,m),(dest,code) in zip(G[v]['successors'],x['successors']):
   expect=[['affine',m]];seen=set()
   while str(t) in d:
    w=str(t);need(w not in seen,'exit cycle');seen.add(w)
    c=d[w];expect.extend([['summary',c['kind']],['affine',c['exit_matrix']]]);t=c['exit']
   need(t==dest and code==expect,'exact summary path program')
 return True
need(validate(D,ranks,A),'certificate')

def execute(code,R):
 for op,arg in code:R=apply(M[arg],R) if op=='affine' else summary(arg,R)
 return R
# Every local loop: exhaustive x,s grid, unrelated registers nonzero.
local=0
for v,c in D.items():
 for x in range(9):
  for s in range(9):
   R=[3]*9;R[6]=x;R[1]=s;w,Q=step(int(v),R);ticks=1
   while str(w)==v:w,Q=step(w,Q);ticks+=1;need(ticks<100,'regression bound')
   need((w,Q)==(c['exit'],apply(M[c['exit_matrix']],summary(c['kind'],R))),'local regression')
   need(ticks==(1 if x==0 else (x+s+1 if c['kind']=='triangular' else x+1)),'exact local duration')
   local+=1
# Entire retained edge programs, including core decrement and all nested summaries.
edges=0;budget_exhausted=0
for v,x in H.items():
 if x['op'][0]=='halt':continue
 for amount in (0,1,2):
  R=[1]*9;R[x['op'][1]]=amount;w,Q=step(int(v),R);ticks=1
  while str(w) in D and ticks<10000:
   w,Q=step(w,Q);ticks+=1
  if str(w) in D:
   budget_exhausted+=1;continue
  b=0 if amount else 1;S=R[:]
  if amount:S[x['op'][1]]-=1
  t,code=x['successors'][b];need((w,Q)==(t,execute(code,S)),'edge regression');edges+=1
bad=[]
def reject(name,d=D,r=ranks,a=A):
 try:validate(d,r,a)
 except ValueError as e:bad.append({'mutation':name,'rejected':True,'reason':str(e)});return
 raise AssertionError(name)
v=next(v for v,d in D.items() if d['kind']=='triangular')
d=copy.deepcopy(D);d[v]['kind']='clear_positive';reject('wrong loop formula',d=d)
r=copy.deepcopy(ranks);r[v]=0;reject('nondecreasing rank',r=r)
a=copy.deepcopy(A);a['nonzero_update']='omit_decrement';reject('missing core decrement',a=a)
a=copy.deepcopy(A)
v=next(v for v,x in H.items() if x['successors'] and len(x['successors'][0][1])>1)
a['nodes'][v]['successors'][0][1].reverse();reject('reversed operation order',a=a)
# Universal simplifications that would be false for arbitrary registers.
zero=[3]*9;zero[6]=0;zero[1]=5
need(summary('triangular',zero)==zero,'zero branch preserves scratch')
pos=[3]*9;pos[6]=1;pos[1]=5
need(summary('triangular',pos)[7]==24,'nonzero scratch included in triangular argument')
for name,obj in [('arithmetic_core.json',A),('summary_certificates.json',D),('summary_ranks.json',ranks)]:
 (B/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
res={'input_sha256':hashlib.sha256(raw).hexdigest(),'input_vertices':len(G),'triangular_loops':sum(x['kind']=='triangular' for x in D.values()),'clear_positive_loops':sum(x['kind']=='clear_positive' for x in D.values()),'remaining_vertices':len(H),'remaining_tests':sum(x['op'][0]=='decnz' for x in H.values()),'remaining_halts':sum(x['op'][0]=='halt' for x in H.values()),'edges':sum(len(x['successors']) for x in H.values()),'max_summary_rank':max(ranks.values()),'local_regressions':local,'core_edge_regressions':edges,'core_edge_regressions_budget_exhausted':budget_exhausted,'adversarial_rejections':bad,'artifact_bytes':(B/'arithmetic_core.json').stat().st_size,'status':'Finite owned Python checks and explicit universal mathematical argument; not kernel compiled.'}
(B/'AUDIT.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
