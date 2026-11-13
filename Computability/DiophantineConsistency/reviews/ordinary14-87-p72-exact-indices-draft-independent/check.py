#!/usr/bin/env python3
"""Independent 87 P72 exact-index binder review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-p72-exact-indices-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','7fe842af8b22e3810c894c42ee9c75c93fa429738c2e4721b0ef467df5a8d1ca')
s=pin(A/'P72ExactIndices87.lean','484ebce47fc957b0d40279de55e9f10206c5be0c1998f5403998e53b8b9c28d7').decode()
pin(A/'check_source.py','329607e9c821c4d35053c8883abeb9517c04cb8b5d891f4168206691d45ffacf')
receipt=pin(A/'observation.json','3047c07b65eff59a88f198f3f9d66968313fc20573de8f9c1d3f8affbcec32f4')
p72=pin(D/'Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3').decode()
assert "theorem indices_ordinary (q X Y k R g c a y0 i' f T u n s μ m η : V)" in p72
for f in ('(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'P72FirstInputs87Draft.first_inputs p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'MainIndex87Draft.main_index p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz',
 'StrongNorm87Draft.strong_norm p v hz',
 'AuxNorm87Draft.aux_norm p beta K MC MF v hport hK hMCcast hMFcast hv hz',
 'P72Exact.indices_ordinary qq xx yy kk R d cc aa s (v 4) (v 3) (v 5) (v 11)',
 'n w (qq^4) m (v 9) hq3 hX hs hYq (hv 9) hc (hv 4) (hv 3) ha',
 'hR26 hny hks hRwindow hnmod hy hnorm hstrong haux',
 'H*(U beta v*v 12+X v*Y v*qq+R+1)'):
 assert f in s,f
assert 'InternalZero (P86ResidueGraph.graph p).output' not in s

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-p72-first-inputs-draft-independent','ordinary14-87-main-index-draft-independent','ordinary14-87-strong-norm-draft-independent','ordinary14-87-aux-norm-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero P72 binder/source review; no Lean or provider replay','component_reviews':4},sort_keys=True,indent=2))
