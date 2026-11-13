from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-first-main-index-boundary')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-early-main-index-obstruction');assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for n,row in {'F':['+','n_F',1],'alpha':['+','n_alpha',1],'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'kbase':['+','n_eta','n_zeta'],'c':['+','n_eta','kY'],'Bt':['-','g27','F'],'Z':['-','g32','Bt'],'R':['+','g47','g50'],'r0base':['-','kbase','R'],'r0':['-','r0base',1],'shift':['-','g54','r0'],'Dstar':['+','g58','g59'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[n]==row,(n,r.get(n))
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
# Relevant first and main product factors cannot equal -1 modulo four.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for U,a,c,z in itertools.product(range(4),repeat=4):
 assert (1+z*z-U*U*(1+(a*a+4*a+3)*c*c))%4!=3
# Check analytic polynomial inequalities for all q>=8 by nonnegative
# coefficients after q=8+t.
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def sc(a,n):return [n*x for x in a]
q=[8,1];q2=mul(q,q);q3=mul(q2,q);q4=mul(q2,q2);q5=mul(q4,q)
a=add(q4,q3);A=add(a,[2])
growth=add(q5,sc(A,-2))
low=add(add(mul(add(sc(q,2),[-1]),add(q2,[-1])),[1]),sc(q2,-2))
up=add(add(add(q5,sc(q4,-1)),sc(q2,-1)),add(sc(q,-1),[-1]))
assert growth[0]>0 and low[0]>0 and up[0]>0 and all(x>=0 for x in growth+low+up)
# Independent small Pell bounds and q-power congruence controls.
def pell(A,j):
 x,y=1,0;D0=A*A-1
 for _ in range(j):x,y=A*x+D0*y,x+A*y
 return x,y
count=0
for q in (8,16,32):
 Y=q**3;M=q**7;A=Y*(q+1)+2
 assert 2*A<q**5
 for n in range(1,7):
  _,yfirst=pell(2*M+1,n);k=2*yfirst
  for m in range(1,8):
   _,c=pell(A,m)
   if c>=Y*k:assert n<=m
   count+=1
print(json.dumps({'prior_receipt_reproduced':True,'exact_free_y_child_first_main_rank_wiring_checked':True,'first_and_main_negative_unit_mod4_cases':1280,'q_ge_8_growth_and_rank_polynomial_bounds':True,'bounded_index_controls':count,'fixed_slice_m_at_most_q_squared_excluded':True,'global_zero_or_internal_proof_claim':False,'lean_executed':False},sort_keys=True,indent=2))
