#!/usr/bin/env python3
"""Independent compact 78↔87 source composition review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-78-87-compact-model-composition-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','f66a3eecabb8fe9ed7fab59b39db7dfc1112912901df3010be7461773476f4ff')
s=pin(A/'Compact78To87.lean','0abd385fa051aa29e8a1caeaa5e73caba008bd03799cae43efe806d1ff61ec0d').decode()
pin(A/'check_source.py','1e5a279d560073b89ed725136c898434841180df6ad2c0067326da5fcb545df2')
receipt=pin(A/'observation.json','94b3a75712ffb7b1b7cb50ba208982ff4b19de68442fc562117540e32bc51d42')
pin(D/'research/ordinary14-78-86-compact-model-composition-draft/Compact78To86.lean','3965881715e791f1b7d3b1c554a26a44fb8f1892d0cbfbe224dcf0447f54590a')
pin(D/'research/ordinary14-86-87-compact-model-equivalence-draft/CompactEquivalence8687.lean','3ba1bb233e7383358ea9bcd4f418eaf13aca1500fc45cc1cb2f981fb4df3c4ff')
for f in ('theorem positive_zero_iff (K : ℕ)','ports CompactFixedBeta.betaNat K lowNat highNat',
 'P78AuxRoot.graph (fun j => (p j : ℤ))','P87ShiftedGuard.graph (fun j => (p j : ℤ))',
 '(Compact78To86Draft.positive_zero_iff K).trans','(CompactEquivalence8687Draft.positive_zero_iff K)'):
 assert f in s,f
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not r.stderr and r.stdout==receipt
print(json.dumps({'scope':'compact 78/87 source composition and author receipt; no Lean','pinned_component_sources':2},sort_keys=True,indent=2))
