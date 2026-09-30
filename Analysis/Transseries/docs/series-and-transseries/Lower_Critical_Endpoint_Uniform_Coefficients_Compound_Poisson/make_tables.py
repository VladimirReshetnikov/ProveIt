#!/usr/bin/env python3
"""Generate the article tables from the recorded verification JSON."""
import json
from pathlib import Path
root=Path(__file__).resolve().parent
j=json.loads((root/'verification_results.json').read_text())
lines=[]
for r in j['coefficients']:
    if not r['prefix'] and r['n'] in [128,2048]:
        lines.append(f"{r['eps']:.3f} & {r['n']} & {r['leading_ratio']:.10f} & {r['corrected_ratio']:.10f} & {r['observed_correction_over_predicted']:.6f} \\\\")
(root/'coefficient_table.tex').write_text('\n'.join(lines)+'\n')
lines=[]
for r in j['landau']['cutoff_diagnostics']:
    if r['z'] in [-2.,0.]:
        lines.append(f"{r['n']} & {r['eps']:.2f} & {r['z']:.0f} & {r['M']} & {r['retained_fraction']:.8f} & {r['limiting_G']:.8f} \\\\")
(root/'landau_table.tex').write_text('\n'.join(lines)+'\n')
print('Generated coefficient_table.tex and landau_table.tex')
