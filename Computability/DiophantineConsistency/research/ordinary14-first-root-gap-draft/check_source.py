from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent;s=(p/'FirstRootGap.lean').read_text()
for t in ('s≤m','8*m+4≤k','hprod','hmul','lt_of_mul_self_lt_mul_self₀','m*k+s<tau'):assert t in s
count=0
for m in range(1,20):
 for k in range(8*m+4,8*m+40):
  for s0 in range(m+1):
   assert 2*m*k+m<=k*k
   assert (m*k+m)**2 < 1+m*(m+1)*k*k
   assert m*k+s0<=m*k+m
   count+=1
print(json.dumps({'square_gap_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'FirstRootGap.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
