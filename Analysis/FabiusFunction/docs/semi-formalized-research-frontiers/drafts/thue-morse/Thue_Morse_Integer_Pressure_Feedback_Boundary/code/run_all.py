"""Quick exact validation of the included analytic and finite certificates."""
from pathlib import Path
import subprocess,sys,json
# ed. (2026-10-01): the checkers now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parent
for name in ['verify_cutoff.py','check_trace_coverage.py','check_m2_response.py','check_m2_pressure.py']:
 # ed. (2026-10-01): the output directory is passed on.
 subprocess.run([sys.executable,str(root/name),'--output-dir',str(out)],check=True)
# ed. (2026-10-01): the final message no longer claims a trace audit that did not take place.
_ed_tc=json.loads((out/'trace_checks.json').read_text())
if not _ed_tc['complete']:print('Trace audit INCOMPLETE:',len(_ed_tc['missing']),'of 68 trace files absent; the other checks passed')
else:print('All packaged certificate checks passed; use reproduce_all.py to regenerate every matrix enclosure')
