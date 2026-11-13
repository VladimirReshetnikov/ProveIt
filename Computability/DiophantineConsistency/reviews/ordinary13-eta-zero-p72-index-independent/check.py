#!/usr/bin/env python3
"""Independent source signature, helper and order-change audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
o=pin('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3')
s=pin('research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src','b02fbec88cc6fbf58651346920fd9626790e623c79bdcb5c2f73f4ff68e88f63')
pin('research/ordinary13-eta-zero-p72-index-draft/result.json','d9bbc68196dd7d6d2b8e0641f743936a1240a79dc5ff7b30e29a4b0508c6155d')
pin('reviews/ordinary13-eta-zero-index-window-audit/result.json','7caf95041a34d783123fa9afc0b6eeac82749511941358a479d42c73a0bd291e')
assert s.startswith('import DiophantineConsistency.Compact44.P72Exact\n') and 'namespace P72ExactEtaNaturalDraft' in s
for name in ['index_window','indices_ordinary']:
 def hdr(t):return t.split('theorem '+name,1)[1].split(':= by',1)[0]
 assert hdr(o).replace('(hη : 0 < η) ','')==hdr(s),name
for name,end in [('large_of_six','/-- The index window:'),('index_close','/-- The index part:')]:
 def piece(t):return t.split('theorem '+name,1)[1].split(end,1)[0]
 assert piece(o)==piece(s),name
assert 'private theorem large_of_six' in s
assert 'have hk0 : 0 < k' in s and s.index('have hk0 : 0 < k')<s.index('have hc0 : 0 < c')
for x in ['mul_pos hY0 hk0','mul_lt_mul_of_pos_left (lt_of_lt_of_le (by norm_num : (1 : V) < 2) hY2) hk0','k * Y ≤ k * Y + η := le_add_of_nonneg_right','hR26 hny hks hnmod hmy','(hc : c = η + Y * k)','signed_half_index_of_facts']:
 assert x in s,x
assert 'hη' not in s
# Each finite order control assumes only the consequences used by the draft.
cases=0
for R in range(26,31):
 for n in range(14,25):
  for k in range(2*n,2*n+6):
   for Y in range(2,8):
    for eta in range(4):
     if R+1>2*n:continue
     c=eta+Y*k
     assert 0<k<c and 2*R<c and 2<=c
     cases+=1
print(json.dumps({'scope':'source signatures and finite order controls; no Lean','only_eta_binder_removed':True,'private_large_of_six_and_index_close_identical':True,'k_positive_before_c_positive':True,'remaining_pell_strong_auxiliary_premises_preserved':True,'eta_zero_included':True,'finite_controls':cases,'lean_elaborated':False},sort_keys=True,indent=2))
