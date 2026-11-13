from pathlib import Path
from hashlib import sha256
from math import comb
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-f-unshift-compact-first-root-n2-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('research/ordinary13-f-unshift-compact-first-root-n2-boundary','reviews/ordinary13-f-unshift-fixed-positive-gap-norm-congruences-independent'):
 p=Path(name);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());r={row[0]:row[1:] for row in g['source']}
for n,row in {'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'C':['-','qF','alpha'],'Bt':['-','g27','n_F'],'k':['+','kbase',1],'ell':['*','E','kY'],'Z':['-','g32','Bt'],'R':['+','g47','g50'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[n]==row
src=Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
assert 'theorem solution_index (b x y : V)' in src and 'ycoord time b=y' in src
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
assert 'xcoord 0 b=1' in rec and 'ycoord 0 b=0' in rec and 'ycoord (time+1) b=' in rec
mask=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text();assert 'range 943 ∪ Ico 983 993' in mask and '}) \\ {1}' in mask
lm=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text();assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in lm
# Independently compute gap polynomials in q, then substitute q=t+2 via
# binomial expansion (different from direct q=[2,1] construction).
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def neg(a):return [-x for x in a]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def scale(a,n):return [x*n for x in a]
def shift2(a):return [sum(a[i]*comb(i,j)*2**(i-j) for i in range(j,len(a))) for j in range(len(a))]
q=[0,1];Y=mul(mul(q,q),q);M=mul(q,mul(Y,Y));A=add(mul(Y,add(q,[1])),[2]);k=add(scale(M,8),[4])
y3=add(scale(mul(A,A),4),[-1]);y4=add(scale(mul(mul(A,A),A),8),neg(scale(A,4)))
lo=add(mul(Y,k),neg(y3));hi=add(y4,neg(mul(add(Y,[1]),k)))
lo2=shift2(lo);hi2=shift2(hi)
assert lo2[0]>0 and hi2[0]>0 and all(v>=0 for v in lo2+hi2)
# Extremal-C rank identity and least nonnegative solution to 2n≡MC (mod q).
count=0
for q in range(2,150,2):
 for MC in range(2,q,2):
  for MF in (0,1,7):
   R=(q*q-q+1)*(q*q-1)+MC+q*MF
   assert R+1-MC==q*(q**3-q*q+1+MF)
   for n in range(0,2*q):
    if (2*n-MC)%q==0:assert n>=MC//2;count+=1
# First-root exact n=2 slice on actual F-probe for varied compact-like ports.
for q in (2,4,8,32):
 beta=q-1;K=9;Y=q**3;M=q*Y*Y;k=8*M+4;tau=8*M*M+8*M+1;h=q+K;rr=(k*beta+1)*h-4*M-3
 w=[1,0,0,1,0,0,1,0,rr,0,k-1,1,0];ports=[beta,K,0,0]
 d=dict(zip(g['witnesses'],w));d.update(zip(g['fixed_numerals'],ports))
 for name,op,a,b in g['source']:
  a=d[a] if isinstance(a,str) else a;b=d[b] if isinstance(b,str) else b
  d[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 assert d['Z']==beta*tau and d['A0']==0 and d['A1']!=0
print(json.dumps({'both_predecessor_receipts_reproduced':True,'actual_first_root_and_rank_rows_checked':True,'independent_q_shift_gap_coefficient_checks':True,'rank_congruence_controls':count,'separate_first_root_graph_controls':4,'fixed_model_or_full_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
