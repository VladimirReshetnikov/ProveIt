from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent;s=(p/'FreshParentRoot.lean').read_text()
for t in ('hb : 0<b','ht : 0<t','m*k+s<tau','pos_iff_one_le.mp hbt','tsub_pos_of_lt hAB','tsub_add_cancel_of_le'):assert t in s
count=0
for m in range(1,12):
 for k in range(1,12):
  for s0 in range(1,5):
   tau=m*k+s0+1
   for b in range(1,5):
    for t in range(1,5):
     A=m*k+k+s0;B=k*b*t+t+tau;r=B-A
     assert r>0 and r+A==B
     count+=1
print(json.dumps({'fresh_root_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FreshParentRoot.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
