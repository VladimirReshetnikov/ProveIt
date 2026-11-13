from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());child=json.loads(Path('research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text())
rows=[]
for row in parent['source']:
 if row==['i','+','n_i',1]:continue
 rows.append(['n_i' if x=='i' else x for x in row])
assert rows==child['source'] and len(rows)==84
# Bounded arithmetic facts only: do not construct 2^m or iterate Pell n,m.
L=2172;n=L*(2*L+1);m=n+L;q=128;beta=127;K0=87;MC=54;MF=139;F=119;alpha=8
assert (n,m)==(9437340,9439512)
R=(alpha+(q-F)*beta)*(q*q-1)+MC+q*MF
assert R==18874679==2*n-1
assert beta>=46 and K0>0 and 0<=MC<beta and beta<=MF<2*beta
assert beta%8==7 and beta%3==1 and MC%8==6 and (MF-beta)%8==4
assert q-F-alpha==1 and L>=3*7 and m%7==5
assert (pow(2,m,beta)+K0-F)%beta==0
assert (m+L+1)*(m-1)==(L+1)+(m+2*L+2)*(n-1)
assert m<2**24 and L+26<m and n>=14
# Exact integer-polynomial identities for root, main shift, and Pell step.
N=8;z=(0,)*N
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
def pol(x):return x if isinstance(x,P) else P({z:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
b,h,k,tau,ell,a,x,y=(var(i) for i in range(N));B=b*h;r=tau-ell-k+(k*b+1)*h
assert b*(ell+k+r-k*B)-B==b*tau
H=3+4*a;Delta=H+a*a;A=a+2;xn=A*x+Delta*y;yn=x+A*y
assert A*A-Delta==1 and xn*xn-Delta*yn*yn==x*x-Delta*y*y
assert xn-a*yn==2*(x-a*y)+H*y and A*yn-xn==y
# Reproduce a small concrete instance of the same power-matching construction.
def pell(A0,j):
 x0,y0=1,0;d=A0*A0-1
 for _ in range(j):x0,y0=A0*x0+d*y0,x0+A0*y0
 return x0,y0
q0=4;L0=6;n0=L0*(2*L0+1);m0=n0+L0;X0=2**m0;Y0=2**L0;M0=X0*Y0*Y0
_,yf=pell(2*M0+1,n0);k0=2*yf;_,c0=pell(Y0*(X0+1)+2,m0)
eta0=c0-Y0*k0;assert 0<eta0<k0
beta0=3;K00=1;MC0=MF0=1;R0=155;U0=Y0*q0*q0
assert R0==2*n0-1 and (2*X0+1)%beta0==0
h0=(2*X0+1)//beta0;tau0,_=pell(2*M0+1,n0);a0=Y0*(X0+1);H0=3+4*a0;g0,_=pell(a0+2,m0)
r0=tau0-M0*k0-k0+(k0*beta0+1)*h0
assert (g0-X0-a0*c0)%H0==0 and (k0-R0-1)%U0==0
gamma0=(g0-X0-a0*c0)//H0+(k0-R0-1)//U0
w0=[1,0,0,1,0,0,X0//q0,0,r0,eta0,k0-eta0,1,gamma0];p0=[beta0,K00,MC0,MF0]
assert min(w0)>=0
def ev(graph):
 d=dict(zip(graph['witnesses'],w0));d.update(zip(graph['fixed_numerals'],p0))
 for name,op,x,y in graph['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
small=ev(child);original=ev(parent)
assert (small['A0'],small['A1'],small['g72'],small['Fa'],small['out'])==(0,0,0,1,0)
assert original['out']==c0**4>0
# Extract source output and shared first/main/strong/aux wire names.
rmap={row[0]:row[1:] for row in child['source']}
for name,row in {'Bt':['-','g27','F'],'R':['+','g47','g50'],'Z':['-','g32','Bt'],'Dstar':['+','g58','g59'],'g72':['-','g71','Q'],'Fa':['-','y2','g82'],'out':['-','P0123',1]}.items():assert rmap[name]==row
print(json.dumps({'ports':[beta,K0,MC,MF],'q':q,'L':L,'first_index':n,'main_index':m,'rank':R,'leading_power_exponents_equal':True,'first_carrier_divisible_by_beta':True,'compact_coarse_inequalities_and_mod8_residues':True,'exact_root_and_pell_step_identities':True,'small_power_matching_full_zero_control':True,'large_pell_coordinates_materialized':False,'fixed_compact_tuple_covered':False,'global_zero_equivalence_refuted':False,'lean_executed':False},sort_keys=True,indent=2))
