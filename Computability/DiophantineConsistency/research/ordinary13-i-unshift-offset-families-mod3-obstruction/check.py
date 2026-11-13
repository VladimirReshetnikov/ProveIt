#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
prev=root/'research/ordinary13-i-unshift-offset-lminus2-mod3-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
# Finite controls; general proof is the symbolic divisibility argument in README.
counts={'h_divisible_3':0,'h_mod9_2_or_5':0}
for h in range(300):
 for L in range(h, h+3*(h+1)+1):
  num=(L-h)*(2*L-h+1)
  if num%(h+1): continue
  n=num//(h+1)
  if h%3==0:
   counts['h_divisible_3']+=1; assert (2*n-1)%3!=0
  if h%9 in (2,5):
   counts['h_mod9_2_or_5']+=1; assert L%3==2 and n%3==0
print(json.dumps({'matched_offsets':'d=L-h',
 'excluded_h_mod9':[0,2,3,5,6], 'rank_assumption':'R=2*n-1',
 'finite_controls':counts,'general_proof':'README symbolic congruences',
 'other_residue_classes_excluded':False,'graph_zero_nonexistence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
