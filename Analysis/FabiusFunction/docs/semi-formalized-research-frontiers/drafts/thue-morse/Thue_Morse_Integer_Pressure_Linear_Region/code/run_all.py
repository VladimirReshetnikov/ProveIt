from pathlib import Path
from fractions import Fraction as Q
import subprocess,sys,json
# ed. (2026-10-01): the checkers now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
ROOT=Path(__file__).resolve().parents[1]
for name in ['verify_saddle.py','verify_linear_strip.py','check_strong_pairs.py']:
 # ed. (2026-10-01): the output directory is passed on; the Schur and identity
 # records checked below are read from data/, as delivered.
 subprocess.run([sys.executable,str(ROOT/'code'/name),'--output-dir',str(out)],check=True)
rows=json.loads((ROOT/'data/fixed_offset_identity_checks.json').read_text())
assert rows['all_checks_passed']and rows['cases']==35
for r in rows['rows']:
 assert Q(r['true_response'])==Q(r['capped_orbit_coefficient'])+Q(r['restored_full_insertion'])-Q(r['feedback'])
print('All 35 saved true-response restoration identities pass')
