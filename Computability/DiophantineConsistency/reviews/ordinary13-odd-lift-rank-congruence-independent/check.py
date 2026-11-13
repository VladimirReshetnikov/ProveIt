from pathlib import Path
from hashlib import sha256
import json,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-odd-lift-rank-congruence-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());r={z[0]:z[1:] for z in p['source']}
for k,v in {'i':['+','n_i',1],'T':['+','n_T',1],'f2':['*','n_f','n_f'],
 'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],
 'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],
 'y2':['*','n_y','n_y'],'V2':['*','V','V'],'g81':['-','y2','V2'],
 'g82':['*','Q','g81'],'Fa':['-','y2','g82'],'g15':['*',4,'a'],
 'H':['+',3,'g15'],'Delta':['+','H','g17'],'a':['+','E','Y'],
 'E':['*','X','Y'],'Y':['*','q3','s'],'s':['+','n_s',1],
 'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],
 'q2':['*','q','q'],'q3':['*','q','q2']}.items():assert r[k]==v,(k,r[k])
def mm(a,b,n):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%n for i in range(2) for j in range(2))
def power(a,k,n):
 z=(1,0,0,1)
 while k:
  if k&1:z=mm(z,a,n)
  a=mm(a,a,n);k//=2
 return z
def pell(A,n):
 x,y=1,0;delta=A*A-1
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
A=2;delta=3;m=3;g,c=pell(A,m);f,v=pell(A,15);I=delta*v
assert (g,c,f,v,I)==(26,15,189750626,109552575,328657725)
assert I%(c*c)==0 and I//(c*c)==1460701 and I*I==delta*(f*f-1)
assert f*f%c==1
ell=218943027;R=12;sigma=-1;M=f*f*c
assert ell%4==3 and (R-m)%c!=0 and (ell+sigma*R)%c==0
main=power((A,delta,1,A),ell,f*f)
assert main[2]==c and (main[2]+sigma*c)%(f*f)==0
# Independent alternative to the reviewed quotient-polynomial recurrence:
# evaluate z_ell modulo I*M, then exact-divide its integer residue by I.
# Since z_ell is an integer multiple of I, this produces (z_ell/I) mod M.
mod=I*M;aux=power((I,I*I-1,1,I),ell,mod);z=aux[0]
assert z%I==0; Wmod=z//I
assert Wmod%(f*f)==(-c)%(f*f) and Wmod%c==3
assert (Wmod+c+f*f*R)%M==0
# Positive representative x_ell(I)/I is positive, so T numerator is positive
# because c,R > 0. No huge auxiliary value is expanded.
assert I>1 and ell>0 and c>0 and R>0
assert ell%3660==1827 and ell%3620==1807 and ell%39660==19827
for q in range(1,6):
 for s in range(1,6):
  for X in range(6):assert q**3*s*(X+1)+2>=3
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'strong_norm_and_positive_integral_i_checked':True,'same_correlated_sign_checked':True,
 'independent_integer_modulus_quotient_checked':True,'compact_graph_A_at_least_three':True,
 'fact_level_only_no_graph_zero':True,'huge_auxiliary_integer_materialized':False,
 'lean_executed':False},indent=2,sort_keys=True))
