#!/usr/bin/env python3
"""Independent circuit, port, degree and finite algebra checks; no Lean."""
import gzip,hashlib,itertools,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():require(sha((r/f).read_bytes())==h,'pin '+f)
def read(f):return json.loads((r/f).read_bytes())
p=read('research/adaptive87-four-square-current88-30/graph.json');g=read('research/adaptive87-four-square-free-positive-ordinate87-36/graph.json')
require(g['witnesses']==[('auxPositive' if n=='u' else n) for n in p['witnesses']] and g['fixed_numerals']==p['fixed_numerals'],'leaf mapping')
require(g['source']==[(['y2','*','auxPositive','auxPositive'] if a[0]=='y2' else a) for a in p['source'] if a[0]!='g78'],'complete DAG edit')
known=set(g['witnesses']+g['fixed_numerals']);rows={};parents={}
for name,op,a,b in g['source']:
 require(name not in known and op in ('+','-','*') and all(type(x)==int or x in known for x in (a,b)),'graph topology')
 known.add(name);rows[name]=(op,a,b);parents[name]=[x for x in (a,b) if isinstance(x,str)]
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in parents:
  if n not in seen:seen.add(n);todo.extend(parents[n])
 else:leaves.add(n)
require(len(seen)==87 and len(g['witnesses'])==13 and set(g['witnesses']+g['fixed_numerals'])<=leaves,'graph liveness')
counts={o:sum(x[1]==o for x in g['source']) for o in '*+-'};require(counts=={'*':48,'+':21,'-':18},'operation census')
def depends(node,target):
 q=[node];seen=set()
 while q:
  n=q.pop()
  if n==target:return True
  if n in seen:continue
  seen.add(n);q.extend(parents.get(n,[]))
 return False
require(not any(depends(n,'auxPositive') for n in ['V','A0','A1','g72']) and depends('Fa','auxPositive'),'witness independence')
# Check all exact residual factor rows that justify the written argument.
expected=[['q','+',1,'qm'],['q2','*','q','q'],['U','*','Y','q2'],['E','*','X','Y'],['a','+','E','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],['c2','*','c','c'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['g74','*','T','c'],['g75','-','g74','R'],['g76','*','f2','g75'],['V','-','g76','c'],['y2','*','auxPositive','auxPositive'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Q','g81'],['Fa','-','y2','g82']]
for n,o,a,b in expected:require(rows.get(n)==(o,a,b),'residual row '+n)
meta=read('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json')['coefficient_binding']['ports'];base=r/'candidates/one-page-padding-staircase-carrier65-2011/coefficients';mod=1000000007;ports={}
for name,v in meta.items():
 z=(base/v['file']).read_bytes();raw=gzip.decompress(z);num=int.from_bytes(raw,'big')
 require(sha(z)==v['gzip_sha256'] and sha(raw)==v['raw_sha256'] and len(raw)==v['raw_bytes'] and num.bit_length()==v['bits'],'port '+name)
 if name=='beta':require(num==2**(47*2011)-1 and num>0,'current beta')
 ports[name]=num%mod
D={n:1 for n in g['witnesses']};D.update({n:0 for n in g['fixed_numerals']});poly={n:[0,1] for n in g['witnesses']};poly.update({n:[v] for n,v in ports.items()})
def get(n):return poly[n] if isinstance(n,str) else [n%mod]
def norm(v):
 while len(v)>1 and v[-1]==0:v.pop()
 return v
for n,o,a,b in g['source']:
 x=get(a);y=get(b);da=D[a] if isinstance(a,str) else 0;db=D[b] if isinstance(b,str) else 0;D[n]=da+db if o=='*' else max(da,db)
 if o=='*':
  z=[0]*(len(x)+len(y)-1)
  for i,u in enumerate(x):
   for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%mod
 else:z=[((x[i] if i<len(x) else 0)+(1 if o=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))]
 poly[n]=norm(z)
require(D[g['output']]==36 and len(poly[g['output']])==37 and poly[g['output']][-1]==57192905,'degree witness')
# Finite controls on exact algebraic identities; these do not replace the proof.
for B,c in itertools.product(range(4,20),range(2,38)):
 lhs=1+(B*B-1)*c*c
 require(lhs-(B*c-1)**2==c*(2*B-c) and (B*c)**2-lhs==c*c-1,'square gap')
for Q,y,V in itertools.product(range(0,8),repeat=3):
 Fa=y*y-Q*(y*y-V*V)
 require((Fa-1)==(V*V-1)-(Q-1)*(y*y-V*V),'aux identity')
print(json.dumps({'scope':'independent graph, port and degree checks; bounded algebra controls, no Lean','pins_sha256':sha((d/'pins.json').read_bytes()),'child_graph_sha256':pins['research/adaptive87-four-square-free-positive-ordinate87-36/graph.json'],'live_gates':len(seen),'counts':counts,'degree_upper':D[g['output']],'degree36_coefficient_mod_1000000007':poly[g['output']][-1],'beta_exact_2_pow_94517_minus_1':True,'ordinate_independence_verified':True},sort_keys=True,indent=2))
