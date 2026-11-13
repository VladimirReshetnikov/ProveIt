from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-generalized-witness-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for dirname in ('ordinary13-independent-k-fixed-point-residue-independent','ordinary13-independent-k-fixed-slice-auxiliary-second-independent'):
 p=Path('reviews')/dirname
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
author=Path('research/ordinary13-independent-k-fixedpoint-full-zero')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(author/'check.py')])==(author/'receipt.json').read_bytes()
certificate=json.loads((author/'receipt.json').read_text())
assert certificate['fixed_point_e']==439547 and certificate['all_fixed_points_mod_N']==[439547]
ind=json.loads(Path('reviews/ordinary13-independent-k-fixed-point-residue-independent/receipt.json').read_text())
mod=ind['N'];A=ind['rank_constant_mod_N'];B=ind['rank_coefficient_mod_N']
found=[];p2=1
for exponent in range(mod):
 if (A-B*p2-exponent)%mod==0:found.append(exponent)
 p2=(2*p2)%mod
assert found==[439547]
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'C':('-','qF','alpha'),'X':('*','q','n_w'),'Y':('*','q3','s'),
 'U':('*','Y','q2'),'G':('+','alpha','g44'),'R':('+','g47','g50'),
 'Bt':('-','g27','F'),'Z':('-','g32','Bt'),'A0':('-','g38','g42'),
 'r0base':('-','n_k','R'),'shift':('-','g54','r0'),'Dstar':('+','g58','g59'),
 'A1':('-','g61','g65'),'g72':('-','g71','Q'),'Fa':('-','y2','g82')}.items():assert rows[n]==row
N=15;zero=(0,)*N
def const(v):return {zero:v} if v else {}
def var(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sgn=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 out={}
 for e,c in a.items():
  for f,d in b.items():
   k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+c*d
 return {k:v for k,v in out.items() if v}
def power(a,k):
 out=const(1)
 for _ in range(k):out=mul(out,a)
 return out
one=const(1);four=const(4)
beta,X,t,L,k,tau,h,q,s,a,H,g0,c,w,z=[var(i) for i in range(N)]
q1=add(beta,one);F=add(L,t);alpha=sub(beta,F);C=sub(sub(q1,F),alpha)
assert C==one
G=add(alpha,mul(sub(q1,F),beta))
assert G==sub(sub(power(q1,2),one),mul(q1,F))
# With w=2^e+beta*z and K0=beta*rho^42+Kprime, the literal
# carrier X+K0-F is beta*(w+rho^42+z), using X=(beta+1)*w.
w0=add(t,mul(beta,z));X0=mul(q1,w0);K0=add(mul(beta,h),L)
assert sub(add(X0,K0),F)==mul(beta,add(add(w0,h),z))
# First carrier and root under h=ρ⁴²+(X−2ʳ)/beta.
r0=add(sub(sub(tau,mul(mul(X,power(q,6)),k)),k),mul(add(mul(k,beta),one),h))
ell=mul(mul(X,power(q,6)),k);B=mul(beta,h)
Z=sub(mul(beta,sub(add(add(ell,k),r0),mul(k,B))),B)
assert Z==mul(beta,tau)
# Generalized scale cancellation: q^5*(4Xq s)=4Xq^6 s.
U=power(q,5);M=mul(X,power(q,6));gamma0=mul(four,mul(mul(X,q),s))
assert mul(U,gamma0)==mul(four,mul(M,s))
# If gamma=gamma0+(g−X−ac)/H, the root collapses to U*g.
Hgamma=add(mul(H,gamma0),sub(sub(g0,X),mul(a,c)))
Dstar=sub(add(mul(U,add(X,mul(a,c))),mul(U,Hgamma)),mul(H,mul(four,mul(M,s))))
assert Dstar==mul(U,g0)
# Generalized coarse growth controls with X>=q, n>=14; powers stay tiny.
for qv in (24,25,32):
 for Xv in (qv,qv+1,2*qv):
  for n in (14,15,20):
   assert Xv**(n-1)>4*qv**3*6**(n-1)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'prior_independent_receipts_reproduced':True,'actual_graph_rows_checked':True,
 'exact_gap_rank_first_root_and_general_scale_polynomials':True,
 'coarse_growth_controls':True,'author_full_witness_receipt_reproduced':True,'all_fixed_points_independently_checked':found,
 'lean_executed':False},sort_keys=True,indent=2))
