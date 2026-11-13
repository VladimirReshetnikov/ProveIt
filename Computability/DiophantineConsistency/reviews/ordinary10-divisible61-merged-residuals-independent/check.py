from pathlib import Path
from hashlib import sha256
import json,sys,resource
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
resource.setrlimit(resource.RLIMIT_AS,(192*1024**2,192*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
D=Path('reviews/ordinary10-divisible61-merged-residuals-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
old=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text())
probe=json.loads(Path('research/ordinary10-divisible61-merged-residuals-spurious/probe.json').read_text())
assert old['domain']==probe['domain']=='nonnegative integers'
assert old['fixed_numerals']==probe['fixed_numerals']==['beta','K0','MC','MF']
assert old['witnesses']==probe['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
expected=[]
for row in old['source']:
 if row[0] in ('Bsq','firstsq'):continue
 if row[0]=='sum1':expected.extend([['merge','+','Bres','firstres'],['mergedsq','*','merge','merge']]);continue
 if row[0]=='out':expected.append(['out','+','mergedsq','A1sq']);continue
 expected.append(row)
assert probe['source']==expected and len(probe['source'])==60 and len(old['source'])==61
# Confirm exact dependence cut supporting the general tau/h transformation.
rows={r[0]:r[1:] for r in old['source']}
def deps(node):
 if isinstance(node,int):return set()
 if node not in rows:return {node}
 op,a,b=rows[node];return deps(a)|deps(b)
assert 'n_tau' not in deps('Bres') and 'n_h' not in deps('firstres')
assert not({'n_h','n_tau'}&deps('A1')) and not({'n_h','n_tau'}&deps('qm'))
assert rows['Bres']==['-','Bt','bh'] and rows['bh']==['*','qm','n_h']
assert rows['firstres']==['-','tausq','g41'] and rows['tausq']==['*','n_tau','n_tau']
# Check the generic algebra independently as polynomial coefficient arrays:
# (tau+b)^2-tau² = b*(2*tau+b), and h change yields its negative.
def add(a,b):return [a[i]+b[i] for i in range(len(a))]
def scale(a,n):return [n*x for x in a]
# Coefficient order: tau², tau*b, b².
newtau2=[1,2,1];oldtau2=[1,0,0];delta=[0,2,1]
assert add(newtau2,scale(oldtau2,-1))==delta and add(delta,scale(delta,-1))==[0,0,0]
# Reconstruct q=4 base witness using linear iteration, not reviewed binary powering.
def pell(A,n):
 x,y=1,0;delta=A*A-1
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
q=4;b=3;X=2**84;Y=64;U=Y*q*q;M=X*Y*Y;a=Y*(X+1);H=4*a+3
assert X%q==0 and Y==q**3
Tau,yFirst=pell(2*M+1,78);k=2*yFirst;root,c=pell(a+2,84);R=155
B=2*(X+1)-1;assert B%b==0;h=B//b
assert (root-X-a*c)%H==0 and (k-R-1)%U==0
gamma=(root-X-a*c)//H+(k-R-1)//U;eta=c-Y*k
vals=[1,0,0,X//q,0,h,Tau,eta,k-eta-1,gamma];ports=[3,1,1,1]
assert all(v>=0 for v in vals+ports)
def evaluate(graph,values):
 e=dict(zip(graph['witnesses'],values));e.update(zip(graph['fixed_numerals'],ports));parents={}
 for name,op,a,b in graph['source']:
  assert name not in e and op in '+-*';parents[name]=(a,b)
  a=a if isinstance(a,int) else e[a];b=b if isinstance(b,int) else e[b]
  e[name]=a+b if op=='+' else a-b if op=='-' else a*b
 live=set();used=set()
 def walk(x):
  if isinstance(x,int):return
  if x not in parents:used.add(x);return
  if x in live:return
  live.add(x)
  for y in parents[x]:walk(y)
 walk(graph['output']);assert len(live)==len(graph['source']) and used==set(graph['witnesses']+graph['fixed_numerals'])
 return e
base=evaluate(old,vals);assert base['out']==base['Bres']==base['firstres']==base['A1']==0
assert base['c']==c and base['Dstar']==U*root and base['k']==k and 84%2==0
changed=vals.copy();changed[5]=h+2*Tau+b;changed[6]=Tau+b
v=evaluate(probe,changed);orig=evaluate(old,changed);d=b*(2*Tau+b)
assert all(x>=0 for x in changed)
assert d>0 and v['Bres']==-d and v['firstres']==d and v['A1']==0
assert v['out']==0 and orig['out']==2*d*d>0
assert v['C']>0 and v['X']>0 and v['k']>v['q']
assert ports[0]>0 and ports[1]>0 and ports[2]<ports[0] and ports[3]<2*ports[0]
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'exact_literal_probe_edits_checked':True,'generic_algebra_and_dependency_cuts_checked':True,
 'q4_base_zero_and_changed_probe_zero_checked':True,'changed_original_positive':True,
 'rows_evaluated':[61,60],'compact_ports_tested':False,'existential_nonequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
