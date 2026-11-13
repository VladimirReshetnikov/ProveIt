from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-y3-signed-main-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-free-aux-square-main-norm-nonsquare-partial','ordinary13-free-aux-square-partial-main-obstruction'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text());r={row[0]:row[1:] for row in g['source']}
for n,row in {'r0base':['-','kbase','R'],'r0':['-','r0base',1],'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'A1':['-','g61','g65']}.items():assert r[n]==row
# Exact y3/x3, norm, and H=4A-5 congruence identities over Z[A].
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def neg(a):return [-x for x in a]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def scale(a,n):return [x*n for x in a]
def clean(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
A=[0,1];a=add(A,[-2]);A2=mul(A,A);Delta=add(A2,[-1]);c=add(scale(A2,4),[-1]);g=add(scale(mul(A2,A),4),neg(scale(A,3)));H=add(scale(A,4),[-5])
assert clean(add(mul(g,g),neg(mul(Delta,mul(c,c)))))==[1]
minus=add(g,neg(mul(a,c)));plus=add(g,mul(a,c))
assert clean(add(minus,[-8]))==clean(mul(H,add(scale(A,2),[2])))
# 8(g+ac)-1 = H*(c²-(2A+2)(g+ac)).
assert clean(add(scale(plus,8),[-1]))==clean(mul(H,add(mul(c,c),neg(mul(add(scale(A,2),[2]),plus)))))
count=0
for q in (16,32,64,128):
 a=q**3*(q+1);A=a+2;H=4*a+3;U=q**5;c=4*A*A-1;g=4*A**3-3*A
 assert 0<q-8<H and 0<8*q+1<H and (g-a*c-8)%H==0
 assert (8*(g+a*c)-1)%H==0
 for m in range(-3,4):
  for gamma in range(4):
   d=q+a*c+H*(gamma-m)
   assert d!=g and d!=-g
   count+=1
print(json.dumps({'two_predecessor_receipts_reproduced':True,'exact_child_main_root_rows_checked':True,'y3_x3_norm_and_signed_residue_polynomial_identities':True,'bounded_signed_root_controls':count,'fixed_y3_slice_A1_excluded':True,'other_main_ordinates_or_full_candidate_excluded':False,'lean_executed':False},sort_keys=True,indent=2))
