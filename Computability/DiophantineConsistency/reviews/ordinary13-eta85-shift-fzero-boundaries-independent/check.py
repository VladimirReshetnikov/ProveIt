from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta85-shift-fzero-boundaries-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-eta85-shift-boundary-probes','ordinary13-eta85-Fzero-positive-gap-boundary'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());probes={}
for gate in ('F','alpha'):
 p=Path('research/ordinary13-eta85-shift-boundary-probes')/(gate+'-probe.json');child=json.loads(p.read_text());probes[gate]=child
 rows=[];inp='n_'+gate
 for n,op,a,b in parent['source']:
  if n==gate:assert [n,op,a,b]==[gate,'+',inp,1];continue
  rows.append([n,op,inp if a==gate else a,inp if b==gate else b])
 assert rows==child['source'] and len(rows)==84
v=[1,0,0,1,0,0,0,0,0,0,0,1,0];ports=[-1,0,1,0]
def ev(g,vals,ports):
 d=dict(zip(g['witnesses'],vals));d.update(zip(g['fixed_numerals'],ports))
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for g in probes.values():
 d=ev(g,v,ports);assert [d[x] for x in ('A0','A1','g72','Fa','out')]==[0,0,0,1,0]
assert ev(parent,v,ports)['out']==9
# Ordered independent source wiring for the F-probe branches.
r={row[0]:row[1:] for row in probes['F']['source']}
for n,row in {'q':['+',1,'qm'],'Y':['*','q3','s'],'k':['+','kbase',1],'C':['-','qF','alpha'],'Bt':['-','g27','n_F'],'Z':['-','g32','Bt'],'G':['+','alpha','g44'],'R':['+','g47','g50'],'r0':['-','kbase','R'],'shift':['-','g54','r0'],'A1':['-','g61','g65']}.items():assert r[n]==row,(n,r.get(n))
# Exact expansion of the first C=0 identity over Z[ell,k,r].
Z=(0,0,0)
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({Z:x})
def var(i):
 e=[0]*3;e[i]=1;return P({tuple(e):1})
ell,k,rr=(var(i) for i in range(3))
assert (ell+k+rr)*(ell+k+rr)-(1+ell*(ell+k))==ell*k+k*k-1+2*rr*(ell+k)+rr*rr
# Verify W bounds and impossibility of q^4 | R under exact port inequalities,
# including q divisible by 3; these are controls, not the universal proof.
count=mult3=0
for beta in range(2,16):
 for J in range(1,6):
  q=1+beta*J
  for MC in range(1,beta):
   for MF in range(2*beta):
    W=J*(MC+q*MF);R=q*q*(q*q-1)+W
    assert 0<W<(q-1)*(1+2*q)<2*q*q
    assert math.gcd(J,q)==1 and R%(q**4)!=0
    count+=1;mult3+=q%3==0
# F=0,C>0 first-factor witness at actual graph and positive natural ports.
for beta in range(1,12):
 for K in range(1,6):
  w=[1,0,0,1,0,0,0,0,(2*beta+1)*K-1,0,1,1,0]
  d=ev(probes['F'],w,[beta,K,0,0])
  assert d['C']==beta and d['k']==2 and d['Z']==beta and d['A0']==0 and d['A1']!=0
print(json.dumps({'both_author_receipts_reproduced':True,'both_exact_shift_row_deltas':True,'two_signed_port_full_zero_controls':True,'Fzero_Czero_first_norm_exact_identity':True,'rank_exclusion_controls':count,'q_divisible_by_three_controls':mult3,'positive_gap_first_norm_controls':55,'fixed_compact_zero_or_reverse_map_proved':False,'lean_executed':False},sort_keys=True,indent=2))
