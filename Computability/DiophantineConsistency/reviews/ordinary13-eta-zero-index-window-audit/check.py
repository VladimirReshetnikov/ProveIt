#!/usr/bin/env python3
"""Source-use inventory and finite inequality controls, not a Lean proof."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3')
p=pin('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390')
o=pin('Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean','913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956')
a=pin('research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean','c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8')
i=s.split('theorem index_window',1)[1].split('theorem index_close',1)[0]
j=s.split('theorem indices_ordinary',1)[1].split('theorem exact_ordinary',1)[0]
assert i.count('hη')==4 and j.count('hη')==3
for x in ['have hc0 : 0 < c','have hkc : k < c','have hhalf : 2 * R < c','have h2n : R + 1 ≤ 2 * n','have hRk : R + 1 ≤ k','have hk0 : 0 < k','have hY2 : 2 ≤ Y']:
 assert x in i,x
for x in ['index_window q X Y','have hc2 : 2 ≤ c','signed_half_index_of_facts']:
 assert x in j,x
assert '(hη : 0 < η)' in i and '(hη : 0 < η)' in j
assert 'theorem power_bound' in p and '(hz : 0<zeta)' in p
assert 'theorem direct_parts_positive' in o and '(hY : 8 ≤ Y) (hk : 0 < k)' in o
assert '(heta : 0<eta)' in a
# k≥R+1 from the early congruence and k=2n+4Qs, then c≥Yk:
# bounded controls cover eta=0 and positive eta; this is not a model proof.
cases=0
for R in range(26,50):
 for mu in range(R+2,R+10):
  for n in range(1,180):
   if (2*n)%mu!=R+1:continue
   for Q in range(1,5):
    for ss in range(4):
     k=2*n+4*Q*ss
     for Y in range(2,9):
      for eta in range(4):
       c=eta+Y*k
       assert R+1<=2*n<=k and 0<k and 2<=Y and Y*k<=c
       assert 0<c and k<c and 2*R<c and 2<=c
       cases+=1
assert cases>0
# Without index/congruence assumptions, eta=0 alone does not imply c>0.
assert 0+27*0==0
print(json.dumps({'scope':'source-use inventory and bounded order controls; no Lean','index_window_eta_uses':3,'indices_ordinary_additional_eta_uses':1,'eta_zero_allowed_by_order_replacements':True,'k_positivity_derived_from_early_index':True,'finite_control_cases':cases,'full_norm_and_graph_binding_not_checked':True,'lean_elaborated':False},sort_keys=True,indent=2))
