"""Fast exact certificate checks; uses only the Python standard library."""
from pathlib import Path
from fractions import Fraction as Q
import json,subprocess,sys
# ed. (2026-10-01): the checkers now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
ROOT=Path(__file__).resolve().parents[1]
for name in ['verify_previous_saddle.py','verify_explicit_strip.py','check_marked_pairs.py']:
 # ed. (2026-10-01): the output directory is passed on; the Schur and identity
 # records checked below are read from data/, as delivered.
 subprocess.run([sys.executable,str(ROOT/'code'/name),'--output-dir',str(out)],check=True)
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
