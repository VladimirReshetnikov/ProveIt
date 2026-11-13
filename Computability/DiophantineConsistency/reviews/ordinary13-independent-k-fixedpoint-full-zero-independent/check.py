from pathlib import Path
from hashlib import sha256
import math,json,re,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixedpoint-full-zero-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for directory in ('research/ordinary13-independent-k-fixedpoint-full-zero','reviews/ordinary13-independent-k-actual-rank-boundary-independent','reviews/ordinary13-independent-k-fixed-slice-auxiliary-discharge-independent','research/ordinary13-independent-k-unit-norm-draft'):
 p=Path(directory);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
root=Path('Lean/DiophantineConsistency/Compact44');N=67*8807;e=439547
rho=pow(2,67,N);q=pow(rho,8807,N);beta=(q-1)%N
# Direct sum of source digit/selector terms modulo N, independently of
# the author's Horner implementation and without materializing constants.
s=(root/'Compact943Data.lean').read_text().split('-- BEGIN PINNED ORDERED ROWS')[1].split('-- END PINNED ORDERED ROWS')[0]
rows=[tuple(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',s)]
src=(root/'CompactSymbolicKernel.lean').read_text();slots=list(map(int,re.search(r'def slots : List ℕ := \[([^]]+)\]',src).group(1).split(',')))
assert len(rows)==943 and len(slots)==41 and all(0<=x<4393 for x in slots)
selector=lambda t:1+2**10*(2**41-(t[0]+2**8*t[1]+2**17*t[2]+2**25*t[3]+127*2**34))
assert all(0<selector(t)<=1+2**51 for t in rows)
kp=(sum(pow(rho,x,N) for x in (30,62,1100,2201,42))+sum(selector(t)*(pow(rho,4393-i,N)+pow(rho,5495-i,N)) for i,t in enumerate(rows))+sum(2**(10+i)*(pow(rho,4393-j,N)+pow(rho,5495-j,N)) for i,j in enumerate(slots)))%N
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
MC=sum((rho-4 if i==1063 else rho-2 if i in support else rho-1)*pow(rho,i,N) for i in range(8807))%N
high=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(high)==8807
H=sum(x*pow(rho,i,N) for i,x in enumerate(high))%N;MF=(beta+H)%N
F=(kp+pow(2,e,N))%N
R=((q*q-1-q*F)*(q*q-1)+MC+q*MF)%N
assert (rho,q,beta,kp,MC,H,MF,F,R)==(299894,273473,273472,551654,428453,73733,347205,16633,439547)
assert R==e and 67*5496<e and e+1<N-1
# Independently expand the carrier, first root and generalized main shift.
N0=11;zero=(0,)*N0
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
 e0=[0]*N0;e0[i]=1;return P({tuple(e0):1})
b,p,z,h0,k,tau,ell,qq,S,a,c=(var(i) for i in range(N0));w=p+b*z;X=(b+1)*w;h=w+h0+z;K0=b*h0
assert X+K0-p==b*h
Bt=b*h;r=tau-ell-k+(k*b+1)*h
assert b*(ell+k+r-k*Bt)-Bt==b*tau
U=qq*qq*qq*qq*qq;M=qq*qq*qq*qq*qq*qq*qq*w
assert 4*M*S==U*(4*qq*qq*w*S)
# Main root after replacing R+1-k=-4*M*S and gamma=4*q²*w*S+z.
H0=3+4*a;main=U*(X+a*c)+H0*(U*(4*qq*qq*w*S+z)-4*M*S)
assert main==U*(X+a*c+H0*z)
# Verify exact graph rows/factor tree at symbolic input names.
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rows0={r[0]:r[1:] for r in g['source']}
for name,row in {'C':['-','qF','alpha'],'Bt':['-','g27','F'],'folded_kBt':['*','n_k','Bt'],'Z':['-','g32','Bt'],'r0base':['-','n_k','R'],'r0':['-','r0base',1],'shift':['-','g54','r0'],'Dstar':['+','g58','g59'],'g72':['-','g71','Q'],'Fa':['-','y2','g82'],'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows0[name]==row
assert g['witnesses']==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_k','n_y','n_gamma']
# Generalized X comparison, including w>1; Pell recurrences remain small.
def pell(A,n):
 x,y=1,0;d=A*A-1
 for _ in range(n):x,y=A*x+d*y,x+A*y
 return x,y
for q0 in (24,30):
 for w0 in (1,2,7):
  n=14;X0=q0*w0;Y=q0**3;M0=X0*Y**2
  tau,y=pell(2*M0+1,n);k0=2*y;g0,c0=pell(Y*(X0+1)+2,2*n-1)
  assert tau*tau==1+M0*(M0+1)*k0*k0
  assert c0>(Y+1)*k0 and c0>X0 and q0**(n-4)>4*6**(n-1)
  assert (g0-Y*(X0+1)*c0-pow(2,2*n-1,3+4*Y*(X0+1)))%(3+4*Y*(X0+1))==0
print(json.dumps({'author_and_three_independent_predecessor_receipts_reproduced':True,'raw_compact_modular_reconstruction':{'q':q,'Kprime':kp,'MC':MC,'high':H,'F':F,'R':R},'fixed_point_e':e,'carrier_first_and_generalized_main_identities':True,'child_factor_and_witness_rows_checked':True,'generalized_pell_growth_and_modular_controls':6,'full_child_zero_claim':'conditional on written general Pell/CRT argument, independently reviewed','actual_large_values_materialized':False,'lean_executed':False},sort_keys=True,indent=2))
