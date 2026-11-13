from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary9-shifted-free-aux-two-norm64-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('research/ordinary9-shifted-free-aux-two-norm64','reviews/ordinary13-free-aux-square-general-completion-second-independent'):
 p=Path(name);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
parent=json.loads(Path('research/ordinary13-shifted85-free-aux-square-criterion/candidate.json').read_text());g=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
expected_inputs=['n_J','n_F','n_alpha','n_w','n_s','n_r','n_eta','n_zeta','n_gamma']
assert g['witnesses']==expected_inputs and len(g['source'])==64 and g['domain']=='nonnegative integers'
assert g['fixed_numerals']==['beta','K0','MC','MF'] and g['fixed_numerals']==parent['fixed_numerals']
rows={row[0]:row[1:] for row in parent['source']}
def ancestors(target):
 seen=set()
 def visit(x):
  if not isinstance(x,str) or x not in rows or x in seen:return
  seen.add(x);_,a,b=rows[x];visit(a);visit(b)
 visit(target);return seen
required=ancestors('A0')|ancestors('A1')
selected=[row for row in parent['source'] if row[0] in required]
assert len(selected)==61 and g['source'][:-3]==selected
assert g['source'][-3:]==[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['out','+','A0sq','A1sq']]
local={r[0]:r[1:] for r in g['source']};visited=set();used=set()
def visit(x):
 if isinstance(x,int):return
 if x in expected_inputs:used.add(x)
 if x in visited or x not in local:return
 visited.add(x);_,a,b=local[x];visit(a);visit(b)
visit('out');assert len(visited)==64 and used==set(expected_inputs)
assert local['s']==['+','n_s',1] and local['k']==['+','kbase',1] and local['c']==['+','n_eta','kY']
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a,c,z in itertools.product(range(4),repeat=4):
 assert (1+z*z-u*u*(1+(a*a+4*a+3)*c*c))%4!=3
# Independent exact univariate ray polynomials at varied fixed port values.
def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
def plus(a,b,sgn=1):
 z=[0]*max(len(a),len(b))
 for i,v in enumerate(a):z[i]+=v
 for i,v in enumerate(b):z[i]+=sgn*v
 return trim(z)
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return trim(z)
for beta,K,MC,MF in [(1,0,0,0),(2,3,4,5),(-3,7,-2,9),(11,-9,8,-4),(0,1,2,3)]:
 p={name:[0] for name in expected_inputs};p.update({'beta':[beta],'K0':[K],'MC':[MC],'MF':[MF]})
 for name in ('n_J','n_w','n_s','n_eta','n_gamma'):p[name]=[0,1]
 for n,op,x,y in g['source']:
  x=p[x] if isinstance(x,str) else [x];y=p[y] if isinstance(y,str) else [y]
  p[n]=plus(x,y) if op=='+' else plus(x,y,-1) if op=='-' else mul(x,y)
 if beta:
  assert len(p['A1'])==31 and p['A1'][-1]==8*beta**21
  assert len(p['out'])==61 and p['out'][-1]==64*beta**42
# Shifted zero-coordinate c>0 is automatic for all nonnegative ports.
for beta in range(5):
 for J in range(5):
  q=1+beta*J
  for s in range(1,5):
   for eta in range(5):
    for zeta in range(5):
     assert eta+q**3*s*(eta+zeta+1)>0
print(json.dumps({'author_and_completion_review_receipts_reproduced':True,'independent_ancestor_projection_exact':True,'live_natural_inputs':len(used),'live_binary_operations':len(visited),'first_main_negative_unit_mod4_cases':1280,'ray_degree_60_varied_port_controls':4,'shifted_c_positive_controls':True,'original_parent_reverse_bridge_proved':False,'lean_executed':False},sort_keys=True,indent=2))
