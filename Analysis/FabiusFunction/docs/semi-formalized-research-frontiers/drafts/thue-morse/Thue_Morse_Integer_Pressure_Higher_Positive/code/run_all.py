from pathlib import Path
import subprocess,sys,json
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
for name in ['explore_higher_pressure.py','check_fourth_response.py','check_m2_cubic.py']:
 subprocess.run([sys.executable,str(ROOT/'code'/name)],cwd=ROOT,check=True,capture_output=True,text=True)
a=json.loads((ROOT/'data'/'fourth_response_checks.json').read_text())
b=json.loads((ROOT/'data'/'m2_negative_higher_certificate.json').read_text())
assert a['all_checks_passed'] and b['all_checks_passed']
assert F(4,9)*F(36,25)**3==F(20736,15625)>1
assert F(7,6)**4*F(4,9)==F(2401,2916)<1
summary={'fourth_response_orders_checked':list(range(2,13)),'second_pressure_coefficient_independently_matched_orders':list(range(2,9)),'small_exception_D_values_verified':True,'uniform_bound_m6_bracket':a['m6_positive_bracket'],'cone_r3_ratio':'20736/15625','negative_m2_t12_cubic_verified':True,'all_checks_passed':True}
(ROOT/'data'/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
