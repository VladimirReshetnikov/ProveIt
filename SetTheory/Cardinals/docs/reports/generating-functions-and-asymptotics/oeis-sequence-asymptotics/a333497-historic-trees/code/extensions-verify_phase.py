#!/usr/bin/env python3
"""Pure-stdlib exact audit of the elementary finite spectral certificates."""
from fractions import Fraction as Q
from pathlib import Path
import json
import os
OUT=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).resolve().parent))
I=Path(os.environ.get("HISTORIC_TREE_INPUT_DIR", OUT))
R=Path(os.environ.get("HISTORIC_TREE_REFERENCE_DIR", Path(__file__).resolve().parents[2] / "data/extensions"))
B=Q(228,25)
L=2*sum((Q(1,(2*k+1)*3**(2*k+1)) for k in range(8)),Q(0))
producer=json.loads((I/'rational_phase_certificates_30_37.json').read_text())
root=json.loads((R/'phase_finite.json').read_text())
out=[]
for r,p,z in zip(range(30,38),producer,root):
    u=[B/j for j in range(r,2*r)]
    phase=sum((sum(((-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(4)),Q(0)) for x in u),Q(0))
    logmod=Q(1,2)*sum((sum(((-1)**(k-1)*x**(2*k)/Q(k) for k in range(1,4)),Q(0)) for x in u),Q(0))
    pg=phase-Q(44,7);mg=L-logmod
    assert pg>Q(1,200) and mg>Q(1,1000)
    assert r==p['r']==z['r']
    assert pg==Q(p['phase_lower_minus_44_over_7'])==Q(z['phase_margin'])
    assert mg==Q(p['log2_lower_minus_logmod_upper'])==Q(z['modulus_margin'])
    out.append({'r':r,'phase_margin':str(pg),'log_modulus_margin':str(mg)})
assert len(producer)==len(root)==8
(OUT/'phase_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all eight exact rational pairs independently recomputed and agree with both existing certificates.')
print('PASS: each phase margin exceeds 1/200; each modulus margin exceeds 1/1000.')
print('Minimum phase margin:',float(min(Q(x['phase_margin']) for x in out)))
print('Minimum modulus margin:',float(min(Q(x['log_modulus_margin']) for x in out)))
