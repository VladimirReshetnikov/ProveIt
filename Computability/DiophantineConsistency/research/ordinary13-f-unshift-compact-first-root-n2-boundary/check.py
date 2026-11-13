from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-f-unshift-compact-first-root-n2-boundary')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'q':('+',1,'qm'),'X':('*','q','n_w'),'Y':('*','q3','s'),
 'C':('-','qF','alpha'),'Bt':('-','g27','n_F'),'ell':('*','E','kY'),
 'Z':('-','g32','Bt'),'a':('+','E','Y'),'Delta':('+','H','g17'),
 'A0':('-','g38','g42'),'A1':('-','g61','g65')}.items():assert rows[n]==row
assert 'theorem solution_index' in Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert (2**67-2)%2==0 and (2**67-2)//2==2**66-1
# For C=q-1, the actual rank obeys R+1-MC=q*(q^3-q²+1+MF).
for q0 in range(2,100):
 for MC in range(q0):
  for MF in (0,1,7):
   R=(q0*q0-q0+1)*(q0*q0-1)+MC+q0*MF
   assert R+1-MC==q0*(q0**3-q0**2+1+MF)
   if MC%2==0 and 0<MC<q0 and q0%2==0:
    for n in range(0,3*q0):
     if (2*n-MC)%q0==0:assert n>=MC//2
# Coefficients after q=2+t: prove Y*k > y_3(A) and y_4(A) > (Y+1)k
# for X=q, Y=q^3, k=8*q*Y^2+4, A=Y*(q+1)+2.
def add(a,b,sign=1):
 d=a+[0]*max(0,len(b)-len(a))
 for i,v in enumerate(b):d[i]+=sign*v
 while len(d)>1 and d[-1]==0:d.pop()
 return d
def mul(a,b):
 d=[0]*(len(a)+len(b)-1)
 for i,v in enumerate(a):
  for j,w in enumerate(b):d[i+j]+=v*w
 while len(d)>1 and d[-1]==0:d.pop()
 return d
def sc(a,k):return [v*k for v in a]
q=[2,1];Y=mul(mul(q,q),q);M=mul(q,mul(Y,Y));A=add(mul(Y,add(q,[1])),[2]);k=add(sc(M,8),[4]);lo=mul(Y,k);hi=mul(add(Y,[1]),k)
y3=add(sc(mul(A,A),4),[1],-1);y4=add(sc(mul(mul(A,A),A),8),sc(A,4),-1)
slack1=add(lo,y3,-1);slack2=add(y4,hi,-1)
assert slack1[0]>0 and all(x>=0 for x in slack1) and slack2[0]>0 and all(x>=0 for x in slack2)
controls=[]
for q0 in (2,4,8,16):
 beta=q0-1;K0=7;X=q0;Y=q0**3;M=X*Y*Y;kk=8*M+4;tau=8*M*M+8*M+1;h=X+K0
 r=(kk*beta+1)*h-4*M-3
 v=[1,0,0,1,0,0,1,0,r,0,kk-1,1,0];ports=[beta,K0,0,0]
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],ports))
 for n,op,x,y in g['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 assert min(v)>=0 and d['C']==beta and d['Bt']==beta*h and d['Z']==beta*tau and d['A0']==0
 aa=Y*(X+1)+2;assert 4*aa*aa-1<Y*kk and (Y+1)*kk<8*aa**3-4*aa
 controls.append({'q':q0,'first_residual':d['A0'],'main_residual_is_nonzero':d['A1']!=0})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'predecessor_receipt_reproduced':True,'actual_F_probe_rows_checked':True,
 'y3_y4_gap_positive_coefficient_certificates':True,'extremal_C_rank_congruence_and_low_digit_lower_bound':True,'exact_first_root_graph_controls':controls,
 'scope':'Actual compact first norm has a solution in this slice; the n=2/X=q/s=1 slice cannot satisfy the main norm.',
 'lean_executed':False},sort_keys=True,indent=2))
