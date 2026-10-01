from pathlib import Path
from fractions import Fraction as Q
import subprocess,sys,json
ROOT=Path(__file__).resolve().parents[1]
for name in ['verify_saddle.py','verify_linear_strip.py','check_strong_pairs.py']:
 subprocess.run([sys.executable,str(ROOT/'code'/name)],check=True)
rows=json.loads((ROOT/'data/fixed_offset_identity_checks.json').read_text())
assert rows['all_checks_passed']and rows['cases']==35
for r in rows['rows']:
 assert Q(r['true_response'])==Q(r['capped_orbit_coefficient'])+Q(r['restored_full_insertion'])-Q(r['feedback'])
print('All 35 saved true-response restoration identities pass')
