#!/usr/bin/env python3
"""Independent 87 conditional main balance source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-main-balance-conditional-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','e8c8496910bb145252a819c2f5929eeac3e2f6bffe32605a7e24d674ba9443b5')
s=pin(A/'MainBalance87.lean','78644fb9163fc15314871598f0e0067453f4cc3551ded62d4270f36a5e42dd87').decode()
pin(A/'check_source.py','24a3c56bf4ea6fbaf73d0cedf1acd6009cee046d2736982c5580d3b877551bfd')
receipt=pin(A/'observation.json','3254662d4cbfa4c2c4c24fb9a9366a500eea58c73110ec9158555a039d5813fc')
for f in ('def X (v : Fin 14 → V) : V := v 6','def Y (v : Fin 14 → V) : V := v 7',
 'ι (X v*Y v*q beta v)', '(hY8 : 8≤Y v)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'NaturalRank87Draft.rank_of_87_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz',
 'main_parts_positive (U beta v) (X v) (Y v) (k v) (v 9) (v 12) (q beta v) R hU hY8 hk',
 'scaled_signed_root (U beta v) (1+Delta v*c v*c v)',
 'rcases hr with h | h'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s
n=0
for X in range(1,5):
 for Y in range(8,12):
  for k in range(1,5):
   eta=1;q=2;U=Y*q*q;R=3;gamma=1;a=X*Y+Y;c=eta+Y*k;H=3+4*a
   rhs=U*(X+a*c)+H*(U*gamma+X*Y*q+R+1)
   assert H*k<rhs;n+=1
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-four-fields-draft-independent','ordinary14-87-natural-rank-draft-independent','ordinary14-scaled-signed-root-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero conditional main-balance source review; no Lean','finite_orientation_cases':n},sort_keys=True,indent=2))
