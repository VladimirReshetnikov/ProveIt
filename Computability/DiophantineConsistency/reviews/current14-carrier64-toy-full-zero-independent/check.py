#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier64-toy-full-zero';graph=root/'research/current14-carrier64-transport-proposal/graph.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(graph)=='f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43';g=json.loads(graph.read_text());rows={r[0]:tuple(r[1:]) for r in g['source']};assert len(rows)==64 and g['output']=='polynomial'
# Independently bind each claimed normal form and final product to named graph operations.
expected={'qm':('*','beta','J'),'q':('+','qm',1),'X':('*','w','q'),'Y':('*','s','q3'),'E':('*','X','Y'),'k':('+','eta','zeta'),'kY':('*','k','Y'),'ell':('*','E','kY'),'c':('+','kY','eta'),'a':('+','E','Y'),'H':('+','four_a',3),'Delta':('+','a2','H'),'main_root':('+','main_base','gammaH'),'R':('+','rproduct','mask'),'tau':('-','tau_partial','R'),'N0':('-','tau2','first_product'),'N1':('-','main_square','Dc2'),'gap':('-','gap_product','C'),'Nt':('-','transport_partial','zqm'),'V':('-','f2inner','c'),'normalized_S':('*','i','Dc2'),'Na':('+','aux_product','y2'),'scaled_Ns':('-','scaled_f2','normalized_S2'),'product0':('*','N0','N1'),'product1':('*','product0','Na'),'product3':('*','product1','Nt'),'product4':('*','product3','scaled_Ns'),'polynomial':('-','product4','Delta')}
for name,expected_row in expected.items():assert rows[name]==expected_row
# Toy-port exact scalar arithmetic, rank and unique same-q,R old coordinates.
beta,K,MC,MF=31,1,22,43;q=beta+1;b=q-1;F,C=2,577;G=q*(q-F)-C;R=G*(q*q-1)+MC+q*MF;N=(R-1)//2
assert (q,G,R,N)==(32,383,393207,196603) and R%4==3 and N%2==1 and R.bit_count()==17 and N.bit_count()==16 and 0<MC<beta<MF<2*beta and MC%4==2 and (MF-beta)%8==4 and MC.bit_count()+(MF-beta).bit_count()==5 and MC+(MF-beta)>beta
wmod=pow(2,R-5,b);Mmod=(K+wmod)%b;assert wmod==4 and (Mmod*C-F)%b==0 and q-F-C==-547
u,r=divmod(G,b);F0=q-u;C0=u-r;assert (u,r,F0,C0)==(12,11,20,1) and (Mmod*C0-F0)%b!=0
# Polynomial Chebyshev recurrence: T_(2n+1)(S)/S = (-1)^n U_(2n)(sqrt(1−S²)).
def plus(a,b,sign=1):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for i,x in a.items():
  for j,y in b.items():c[i+j]=c.get(i+j,0)+x*y
 return {k:v for k,v in c.items() if v}
def sc(a,v):return {k:x*v for k,x in a.items() if x*v}
Q0={0:1};Q1={1:4,0:-3};u0={0:1};u2={0:3,1:-4} # even U₂(sqrt(1−v))
for n in range(1,45):
 assert Q1==sc(u2,(-1)**n) and Q1.get(0,0)==(-1)**n*(2*n+1)
 Q0,Q1=Q1,plus(mul({1:4,0:-2},Q1),Q0,-1)
 u0,u2=u2,plus(mul({0:2,1:-4},u2),u0,-1)
# Recheck the auxiliary unit divisibilities and every norm on independently chosen small main units.
def pmul(a,b,D):return (a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def power(a,k,D):
 z=(1,0)
 while k:
  if k&1:z=pmul(z,a,D)
  a=pmul(a,a,D);k//=2
 return z
for a in range(1,7):
 Delta=(a+2)**2-1
 for R0 in ((3,5) if a==1 else (3,)):
  D,c=power((a+2,1),R0,Delta);assert D*D-Delta*c*c==1
  f,L=power((D,c),c,Delta);assert L%(c*c)==0 and f*f-Delta*L*L==1
  S=Delta*L;v,y=power((S,1),R0,S*S-1);assert v%S==0;V=v//S
  sign=(-1)**((R0-1)//2);assert (V-sign*c)%(f*f)==0 and (V-sign*R0)%c==0 and (f*f-1)%c==0 and v*v-(S*S-1)*y*y==1
# The huge symbolic Pell power is not expanded; proofs for all indices use recurrence induction.
for f in ('current14-carrier64-transport-proposal-independent','current14-carrier64-pell-floor-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
rp=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not rp.stderr and json.loads(rp.stdout)==json.loads((pkg/'result.json').read_text()) and json.loads(rp.stdout)['checker_sha256']==sha(pkg/'check.py')
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'symbolic full candidate zero at toy ports only; same-q,R,w old repair impossible; current-port and unrestricted existential reverse equivalence remain open; no Lean'},indent=2))
