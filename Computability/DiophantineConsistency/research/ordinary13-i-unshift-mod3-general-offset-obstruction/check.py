from pathlib import Path
from hashlib import sha256
import math,json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-i-unshift-mod3-general-offset-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-i-unshift-more-power-offset-obstructions')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
assert [(L*L+2*L+2)%3 for L in range(3)]==[2,2,1]
assert [((L-2)*(2*L-1))%3 for L in range(3)]==[2,2,0]
count=div3=0
for L in range(2,500):
 for h in range(1,L+1):
  d=L+1-h;num=d*(d+L+1)
  if num%h:continue
  n=num//h;R=2*n-1
  if h%3==1:
   assert R%3!=0;count+=1
  if h%3==0 and h%9!=0:
   u=h//3;assert math.gcd(u,3)==1 and L%3==2 and n%3==0 and R%3==2
   div3+=1
print(json.dumps({'prior_receipt_reproduced':True,'matched_offsets_checked_h_one_mod_three':count,'matched_offsets_checked_h_divisible_3_not_9':div3,'excluded_h_classes_mod9':[1,3,4,6,7],'J_scope':'any natural J with fixed compact ports and q a power of two','global_graph_zero_nonexistence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
