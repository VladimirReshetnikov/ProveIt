"""Check diagnostic stability under independent quadrature refinement."""
import json
from pathlib import Path
root=Path(__file__).resolve().parent
lo=json.loads((root/'fourier_sector_diagnostics.json').read_text())
hi=json.loads((root/'quadrature_refinement_diagnostics.json').read_text())
assert lo['quadrature_order']==160 and hi['quadrature_order']==192
assert len(lo['sector_cases'])==len(hi['sector_cases'])==7
keys=['n','j','central_exact_Bessel_integral_over_Mj','expected_c1_c2_c3']
for a,b in zip(lo['sector_cases'],hi['sector_cases']):
    for key in keys:assert a[key]==b[key],(key,a[key],b[key])
print('PASS: all seven central exact-Bessel integral ratios agree to the displayed 26 digits under 160-to-192-node refinement')
assert lo['wedge_cases']==hi['wedge_cases']
print('PASS: all nine complex-wedge checks reproduce')
