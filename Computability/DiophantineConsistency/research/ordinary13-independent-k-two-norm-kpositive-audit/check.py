from pathlib import Path
from hashlib import sha256
from math import gcd
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-two-norm-kpositive-audit')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text()); rows={x[0]:x[1:] for x in g['source']}
assert len(rows)==84 and g['domain']=='nonnegative integers'
expected={'qm':['*','n_J','beta'],'q':['+',1,'qm'],'F':['+','n_F',1],'alpha':['+','n_alpha',1],
'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],
'Y':['*','q3','s'],'U':['*','Y','q2'],'qF':['-','q','F'],'C':['-','qF','alpha'],
'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],
'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],
'kY':['*','Y','n_k'],'ell':['*','E','kY'],'g30':['+','ell','n_k'],
'g31':['+','g30','n_r'],'folded_kBt':['*','n_k','Bt'],'folded_g31':['-','g31','folded_kBt'],
'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],'g38':['*','Z','Z'],
'g39':['*','qm','qm'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],
'g42':['*','g39','g41'],'A0':['-','g38','g42'],'g44':['*','qF','qm'],
'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],
'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','n_J','g49'],
'R':['+','g47','g50'],'r0base':['-','n_k','R'],'r0':['-','r0base',1],
'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g19':['*','a','c'],
'b0':['+','X','g19'],'g58':['*','U','b0'],'g59':['*','H','shift'],
'Dstar':['+','g58','g59'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],
'c':['+','n_eta','kY'],'c2':['*','c','c'],'g17':['*','a','a'],
'Delta':['+','H','g17'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],
'g65':['*','g62','g64'],'A1':['-','g61','g65']}
for n,v in expected.items():assert rows[n]==v,(n,rows[n])
assert 'theorem port_bounds' in Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
assert 'theorem K_pos' in Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
# Sparse integer polynomials establish inequalities with positive slack variables.
N=5;z=(0,)*N
def cn(n):return {z:n} if n else {}
def var(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 r=a.copy()
 for e,c in b.items():r[e]=r.get(e,0)+sign*c
 return {e:c for e,c in r.items() if c}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 r={}
 for e,c in a.items():
  for f,d in b.items():
   k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,0)+c*d
 return {e:c for e,c in r.items() if c}
one=cn(1);two=cn(2);q2=lambda a:mul(a,a)
f,al,c,_,_=[var(i) for i in range(N)]
F=add(one,f);alpha=add(one,al);C=add(one,c);q=add(add(F,alpha),C)
G=add(alpha,mul(sub(q,F),sub(q,one)))
assert all(x>=0 for x in sub(sub(q2(q),two),G).values())
# Exceptional branch: d=1+D, t=-C, b=1+t*d+e from F=b-t*d>=1.
D0,t,e,_,_=[var(i) for i in range(N)];d=add(one,D0);b=add(add(one,mul(t,d)),e);q=add(one,b)
F=sub(b,mul(t,d));alpha=add(one,mul(t,add(d,one)));G=add(alpha,mul(sub(q,F),b))
assert G==add(q,mul(t,add(one,mul(q,d))))
assert all(x>=0 for x in sub(sub(q2(q),two),G).values())
# Worst rank bound equals q^4-q^2-q+2, strictly less than q^4 for q>=2.
u=var(0);q=add(two,u);q_sq=q2(q)
rank_cap=add(add(mul(sub(q_sq,two),sub(q_sq,one)),mul(sub(q,one),add(one,mul(two,q)))),one)
slack=sub(q2(q_sq),rank_cap)
assert slack==sub(add(q_sq,q),two) and slack.get(z,0)>0 and all(x>=0 for x in slack.values())
# Arithmetic controls for gcd and the bounds, including both first-root branches.
for q in range(2,150):
 for a in range(0,150,q**3):
  assert gcd(3+4*a,q**5) in (1,3) and q%gcd(3+4*a,q**5)==0
count=0
for beta in range(1,9):
 for J in range(1,5):
  b=J*beta;q=b+1
  for K in range(1,5):
   for w in range(4):
    d=q*w+K
    for F in range(1,q+3):
     for alpha in range(1,q+3):
      C=q-F-alpha;B=C*d-F
      # k=0 first norm admits these two possible root values.
      if B%b:continue
      m=B//b
      if m < -1:continue
      if C<=0:assert m==-1 and B==-b and -C>=0
      G=alpha+(q-F)*b
      assert 0<G<=q*q-2
      for MC,MF in ((0,0),(beta-1,2*beta-1)):
       R=G*(q*q-1)+J*(MC+q*MF)
       assert 0<R+1<q**4;count+=1
source=Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
assert 'CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in source
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'actual_graph_wiring_checked':True,'two_case_G_nonnegative_coefficient_certificates':True,
 'strict_rank_cap_certificate':True,'bounded_branch_checks':count,
 'bounded_gcd_controls':True,'compact_bound_declarations_observed':True,
 'claim':'Ordinary-integer A0=A1=0 forces k>0 under the stated natural-port bounds; no factor extraction assumed.',
 'lean_executed':False},sort_keys=True,indent=2))
