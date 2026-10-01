"""Fast exact certificate checks; uses only the Python standard library."""
from pathlib import Path
from fractions import Fraction as Q
import json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
for name in ['verify_previous_saddle.py','verify_explicit_strip.py','check_marked_pairs.py']:
 subprocess.run([sys.executable,str(ROOT/'code'/name)],check=True)
count=0
for m in range(2,15):
 d=json.loads((ROOT/'data'/f'schur_m{m:03}.json').read_text())
 assert d['m']==m and d['exact_direct_phase_comparison']
 assert len(d['pressure'])==2*m-1
 for p,piece in zip(d['pressure'],d['pieces']):
  assert Q(p)==Q(piece['frozen'])-Q(piece['feedback'])-Q(piece['cosine'])>0
  count+=1
assert count==195
rows=json.loads((ROOT/'data/fixed_offset_identity_checks.json').read_text())
assert rows['cases']==35 and rows['all_checks_passed']
for d in rows['rows']:
 assert Q(d['true_response'])==Q(d['capped_orbit_coefficient'])+Q(d['restored_full_insertion'])-Q(d['feedback'])
print('All 195 stored Schur pressure coefficients and 35 restoration identities pass')
