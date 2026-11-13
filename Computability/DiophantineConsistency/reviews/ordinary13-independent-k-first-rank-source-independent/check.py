from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import subprocess,sys,json
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-first-rank-source-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-first-rank-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(p/'IndependentKFirstRank.lean.src').read_text()
assert "have halpha : A≤Q-F'-1 := by dsimp [C] at hc; linarith" in s
assert 'IndependentKZeroMainRankDraft.zero_k_impossible q X Y s R eta gamma z hqpos hs hY hR hshape hnorm' in s
# Ordered-field countermodel to the strict-to-unit step when discreteness of
# embedded naturals is not supplied to linear arithmetic.
Q,B,F0,A,D0,r=F(4),F(3),F(1),F(5,2),F(1),F(5,6)
C=Q-F0-A;P=C*D0-F0
assert B>0 and Q==B+1 and F0>=1 and A>=1 and D0>=1 and r>=0
assert C>0 and (B*r-P)**2==B*B and not (A<=Q-F0-1)
# Integer controls check the first-norm coefficient on both branches.
npos=nnon=0
for beta in range(1,8):
 for J in range(1,5):
  q=beta*J+1;b=q-1
  for F0 in range(1,q+3):
   for alpha in range(1,q+3):
    C=q-F0-alpha
    for d in range(1,5):
     P=C*d-F0
     for r in range(4):
      if (b*r-P)**2!=b*b:continue
      G=alpha+(q-F0)*b
      assert G<=q*q-2
      if C>0:npos+=1
      else:
       nnon+=1; assert r==0 and P==-b
       t=-C
       assert F0==b-t*d and alpha==1+t*(d+1)
       assert G==q+t+q*t*d
# Independent strict rank-margin algebra for all small model-natural masks.
count=0
for beta in range(1,11):
 for J in range(1,8):
  q=beta*J+1
  for MC in range(beta):
   for MF in range(2*beta):
    G=q*q-2
    R=G*(q*q-1)+J*(MC+q*MF)
    assert R+1<q**4
    count+=1
print(json.dumps({'author_receipt_reproduced':True,'positive_gap_rational_countermodel_to_implicit_discreteness':True,'positive_C_integer_norm_controls':npos,'nonpositive_C_integer_norm_controls':nnon,'rank_upper_bound_controls':count,'main_helper_argument_order_checked':True,'lean_executed':False,'elaboration_or_provider_verified':False},sort_keys=True,indent=2))
