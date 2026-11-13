from pathlib import Path
from hashlib import sha256
import itertools,json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-f-unshift-strong-aux-necessary-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-f-unshift-fixed-strong-aux-necessary-condition')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'kbase':('+','n_eta','n_zeta'),'k':('+','kbase',1),'i':('+','n_i',1),
 'T':('+','n_T',1),'Q':('*','Delta','rho'),'g72':('-','g71','Q'),
 'V':('-','g76','c'),'Fa':('-','y2','g82'),'F0':('+',1,'A0'),
 'F1':('+',1,'A1'),'Fs':('+',1,'g72'),'out':('-','P0123',1)}.items():assert r[n]==row
# Independent exhaustive residue signs over all f,I,d,z modulo 8/4.
assert all((1+I*I-3*(f*f-1))%8!=7 for f,I in itertools.product(range(8),repeat=2))
for f,I in itertools.product(range(8),repeat=2):
 if (1+I*I-3*(f*f-1))%8==1:
  assert (f%2==1 and I%4==0) or (f%4==2 and I%2==1)
assert all((1+d*d)%4!=3 for d in range(4))
assert all((1+z*z-beta*beta*(1+ell*(ell+k)))%4!=3
 for z,beta,k in itertools.product(range(4),(1,3),range(4)) for ell in (0,4))
# Model-free integer controls for c>a+2 and corrected f²>c+1 bounds.
for X in range(1,8):
 for Y in range(8,18):
  M=X*Y*Y;k=8*M+4;c=Y*k;a=Y*(X+1);Delta=(a+2)**2-1
  assert c>a+2 and Delta<c*c and c**4>Delta*c*c
# Auxiliary Pell alternating modulo I and source statement.
assert 'theorem solution_index' in Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
for I in range(2,40):
 x,y=1,0
 for m in range(30):
  assert (x%I==0)==(m%2==1)
  if m>0:assert y>0
  x,y=I*x+(I*I-1)*y,x+I*y
# Direct finite arithmetic controls for y=1 exclusion via f²>c+1.
for c in range(2,50):
 for f2 in range(c+2,100):assert (-c)%f2 not in (1,(f2-1)%f2)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'actual_literal_rows_checked':True,
 'factor_residue_sign_exhausted':True,'corrected_growth_bound_controls':True,
 'auxiliary_Pell_odd_index_controls':True,'y_equals_one_exclusion_controls':True,
 'scope':'Standard-integer necessary condition under fixed ports and actual zero; no existence or model proof.',
 'lean_executed':False},sort_keys=True,indent=2))
