from pathlib import Path
import json
p=Path(__file__).resolve().parent
old=(p.parent/'ordinary14-87-guard-strict-draft/GuardStrict87.lean').read_text()
new=old.replace('conditional on X≥q²','conditional on X≥q').replace('an explicit X≥q² bound','an explicit X≥q bound').replace('GuardStrict87Draft','GuardStrict87LinearDraft').replace('(hX : q beta v*q beta v≤v 6)','(hX : q beta v≤v 6)').replace('  have hq1 : 1≤qq := pos_iff_one_le.mp hq0\n','').replace('  have hqq : qq≤qq*qq := le_mul_of_one_le_right (Arithmetic.zero_le qq) hq1\n','').replace('lt_of_lt_of_le hF (le_trans hqq hX)','lt_of_lt_of_le hF hX')
assert (p/'GuardStrict87Linear.lean').read_text()==new
count=0
for b in range(1,10):
 q=b+1
 for F in range(1,q):
  for alpha in range(1,q-F):
   C=q-F-alpha
   for X in range(q,q+5):
    for K in range(7):
     num=C*(X+K*q)-F
     if num>0 and num%b==0:
      omega=num//b
      assert C*K<omega
      count+=1
print(json.dumps({'source_delta_exact':True,'positive_guard_cases':count,'lean_run':False},sort_keys=True,indent=2))
