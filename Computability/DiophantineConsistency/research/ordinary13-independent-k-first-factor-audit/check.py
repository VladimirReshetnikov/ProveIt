from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-first-factor-audit')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for name,row in {'kY':['*','Y','n_k'],'ell':['*','E','kY'],'g30':['+','ell','n_k'],'g31':['+','g30','n_r'],'folded_kBt':['*','n_k','Bt'],'folded_g31':['-','g31','folded_kBt'],'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'g38':['*','Z','Z'],'g39':['*','qm','qm'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],'g42':['*','g39','g41'],'A0':['-','g38','g42']}.items():assert r[name]==row,(name,r[name],row)
# Exact integer polynomials in beta,K0,MC,MF,eta,gamma,n_s.
N=7;zero=(0,)*N
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
def pol(x):return x if isinstance(x,P) else P({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
b,K0,MC,MF,eta,gamma,s0=(var(i) for i in range(N));q=b+1
ws=[1,b-1,0,0,0,0,0,s0,0,eta,0,0,gamma];ps=[b,K0,MC,MF]
d=dict(zip(g['witnesses'],ws));d.update(zip(g['fixed_numerals'],ps))
for name,op,x,y in g['source']:
 x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
 d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 if name=='Dstar':break
Y=q*q*q*(s0+1);U=Y*q*q;H=3+4*Y;R=q*(q*q-1)+MC+q*MF
for name,want in [('qm',b),('q',q),('X',0),('C',0),('Bt',-b),('Z',b),('A0',0),('Y',Y),('U',U),('H',H),('R',R),('c',eta),('Dstar',U*Y*eta+H*(U*gamma+R+1))]:assert d[name]==want,name
beta_src=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
print(json.dumps({'first_factor_graph_binding_checked':True,'exceptional_partial_assignment_symbolic':True,'main_root_rank_symbolic':True,'excluded_partial_family':'eta in 1..q, natural ports and gamma, by explicit main-norm inequality','full_graph_zero_claim':False,'all_k_zero_cases_excluded':False,'lean_executed':False},sort_keys=True,indent=2))
