from pathlib import Path
import subprocess,sys
# ed. (2026-10-01): the checkers and their console logs now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parent
# ed. (2026-10-01): the output directory replaces data/ here (created above).
for script in ['check_second_response.py','check_orbit_coefficients.py','check_large_orders.py','check_finite_basis.py','check_finite_formula.py']:
 # ed. (2026-10-01): the output directory is passed on, and each log is written there with LF.
 r=subprocess.run([sys.executable,str(root/script),'--output-dir',str(out)],capture_output=True,text=True)
 (out/(Path(script).stem+'.log')).write_bytes((r.stdout+r.stderr).encode('utf-8'))
 if r.returncode:
  print(r.stdout+r.stderr);raise SystemExit(r.returncode)
 print(script+': passed')
