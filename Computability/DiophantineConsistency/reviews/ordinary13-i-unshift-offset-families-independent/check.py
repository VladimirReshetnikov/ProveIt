from pathlib import Path
from hashlib import sha256
import json,sys,math,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-i-unshift-offset-families-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('research/ordinary13-i-unshift-offset-families-mod3-obstruction','research/ordinary13-i-unshift-mod3-general-offset-obstruction'):
 p=Path(name);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
other={0,2,3,5,6};ours={1,3,4,6,7};assert {(h+1)%9 for h in other}==ours
# Independently compare both notations and every eligible integral match
# in a bounded grid, including exact division before reducing modulo three.
counts={'denominator_coprime3':0,'denominator_v3_one':0}
for ha in range(300):
 H=ha+1
 for L in range(ha,ha+301):
  d=L-ha;num=d*(2*L-ha+1)
  assert d==L+1-H and d+L+1==2*L-ha+1
  if num%H:continue
  n=num//H;R=2*n-1
  if ha%3==0:
   assert H%3==1 and n%3==(L*(2*L+1))%3 and R%3!=0
   counts['denominator_coprime3']+=1
  if ha%9 in (2,5):
   kk=(ha-2)//3;assert (kk+1)%3!=0 and L%3==2
   tt=(L-2)//3
   assert n*(kk+1)==3*(tt-kk)*(2*tt-kk+1)
   assert n%3==0 and R%3==2
   counts['denominator_v3_one']+=1
print(json.dumps({'both_independent_author_receipts_reproduced':True,'other_offset_h': 'L-d','previous_offset_H':'L+1-d','offset_relation':'H=h+1','excluded_residue_classes_equivalent':True,'bounded_integral_match_controls':counts,'graph_zero_nonexistence_or_model_proved':False,'lean_executed':False},sort_keys=True,indent=2))
