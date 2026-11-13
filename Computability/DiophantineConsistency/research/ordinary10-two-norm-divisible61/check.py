from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-two-norm-divisible61')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary9-shifted-free-aux-two-norm64')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads((p/'candidate.json').read_text());h=json.loads((D/'candidate.json').read_text())
assert len(g['source'])==64 and len(h['source'])==61 and len(h['witnesses'])==10
assert h['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
remove={'g31','folded_kBt','folded_g31','g32','Z','g38','g39','g42','A0','A0sq','A1sq','out'}
rows=[]
for row in g['source']:
 n=row[0]
 if n in remove:continue
 rows.append(row)
 if n=='Bt':rows.extend([['bh','*','qm','n_h'],['Bres','-','Bt','bh']])
 if n=='g41':rows.extend([['tausq','*','n_tau','n_tau'],['firstres','-','tausq','g41']])
rows += [['Bsq','*','Bres','Bres'],['firstsq','*','firstres','firstres'],['A1sq','*','A1','A1'],['sum1','+','Bsq','firstsq'],['out','+','sum1','A1sq']]
assert rows==h['source'] and h['fixed_numerals']==g['fixed_numerals']
index={n:(op,a,b) for n,op,a,b in rows};inputs=set(h['witnesses']);live=set();used=set()
def visit(n):
 if isinstance(n,int):return
 if n in inputs:used.add(n)
 if n in live or n not in index:return
 live.add(n);_,a,b=index[n];visit(a);visit(b)
visit('out');assert len(live)==61 and used==inputs
# A1 ordered tree is exactly the parent's A1 tree.
def tree(graph,target):
 d={x:('v',x) for x in graph['witnesses']};d.update({x:('p',x) for x in graph['fixed_numerals']})
 for n,op,a,b in graph['source']:
  d[n]=(op,d[a] if isinstance(a,str) else a,d[b] if isinstance(b,str) else b)
  if n==target:return d[n]
assert tree(g,'A1')==tree(h,'A1')
# Exact normalized root reconstruction polynomial.
N=5;zero=(0,)*N
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 d=a.copy()
 for x,v in b.items():d[x]=d.get(x,0)+sign*v
 return {x:v for x,v in d.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 d={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));d[k]=d.get(k,0)+v*w
 return {k:v for k,v in d.items() if v}
b,hh,ell,k,tau=[V(i) for i in range(N)];Bt=mul(b,hh)
r=add(sub(sub(tau,ell),k),add(mul(mul(k,b),hh),hh))
Z=sub(mul(b,sub(add(add(ell,k),r),mul(k,Bt))),Bt)
assert Z==mul(b,tau)
# First Pell controlled identities and positive reconstructed r.
controls=0
for M in range(1,20):
 A=2*M+1;delta=M*(M+1);x,y=1,0
 for n in range(1,5):
  x,y=A*x+2*delta*y,2*x+A*y
  assert x*x==1+delta*y*y
  for b0 in range(1,6):
   for h0 in range(1,6):
    ell0=M*y;r0=x-ell0-y+y*b0*h0+h0
    assert r0>=0 and b0*(ell0+y+r0-y*b0*h0)-b0*h0==b0*x
    controls+=1
# Exact beta-symbolic ray: 61-output coefficient of t^60 is 64 beta^42.
def C2(v):return {(0,0):v} if v else {}
def add2(a,b,sign=1):
 d=a.copy()
 for e,v in b.items():d[e]=d.get(e,0)+sign*v
 return {e:v for e,v in d.items() if v}
def mul2(a,b):
 d={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():d[(i+k,j+l)]=d.get((i+k,j+l),0)+v*w
 return {e:v for e,v in d.items() if v}
d={x:{} for x in h['witnesses']+h['fixed_numerals']};d['beta']={(0,1):1}
for n in ('n_J','n_w','n_s','n_eta','n_gamma'):d[n]={(1,0):1}
for n,op,x,y in rows:
 x=d[x] if isinstance(x,str) else C2(x);y=d[y] if isinstance(y,str) else C2(y)
 d[n]=add2(x,y) if op=='+' else add2(x,y,-1) if op=='-' else mul2(x,y)
assert max(i for i,j in d['out'])==60 and {k:v for k,v in d['out'].items() if k[0]==60}=={(60,42):64}
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'parent_receipt_reproduced':True,'live_inputs':len(used),'live_operations':len(live),
 'unchanged_main_tree':True,'exact_root_reconstruction_polynomial':True,
 'first_norm_reconstruction_controls':controls,'degree_for_nonzero_beta':60,
 'standard_zero_equivalence_domain':'natural ports beta>0 and K0>0',
 'original_parent_reverse_bridge_proved':False,'lean_executed':False},sort_keys=True,indent=2))
