from pathlib import Path
import subprocess,sys,json
from fractions import Fraction as F
# ed. (2026-10-01): the checkers and this summary now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
ROOT=Path(__file__).resolve().parents[1]
for name in ['explore_higher_pressure.py','check_fourth_response.py','check_m2_cubic.py']:
 # ed. (2026-10-01): the output directory is passed on; the two results are read back from it.
 subprocess.run([sys.executable,str(ROOT/'code'/name),'--output-dir',str(out)],cwd=ROOT,check=True,capture_output=True,text=True)
a=json.loads((out/'fourth_response_checks.json').read_text())
b=json.loads((out/'m2_negative_higher_certificate.json').read_text())
assert a['all_checks_passed'] and b['all_checks_passed']
assert F(4,9)*F(36,25)**3==F(20736,15625)>1
assert F(7,6)**4*F(4,9)==F(2401,2916)<1
summary={'fourth_response_orders_checked':list(range(2,13)),'second_pressure_coefficient_independently_matched_orders':list(range(2,9)),'small_exception_D_values_verified':True,'uniform_bound_m6_bracket':a['m6_positive_bracket'],'cone_r3_ratio':'20736/15625','negative_m2_t12_cubic_verified':True,'all_checks_passed':True}
# ed. (2026-10-01): written to the output directory with LF.
(out/'verification.json').write_bytes((json.dumps(summary,indent=2)+'\n').encode('utf-8'))
print(json.dumps(summary,indent=2))
