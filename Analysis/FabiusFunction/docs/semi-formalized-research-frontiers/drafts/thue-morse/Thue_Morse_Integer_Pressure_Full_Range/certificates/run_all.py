"""Replay every scalar proof certificate with the Python standard library."""
from pathlib import Path
import subprocess,sys
# ed. (2026-10-01): the checkers now write to <output-dir>, by
# default rerun/ beside this program, with LF line endings (as delivered they overwrote the
# recorded files beside themselves, with CRLF on Windows). Pass --output-dir with this program's
# directory, on a copy, to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parent
for name in ['verify_green_constants.py','verify_weighted_outer.py',
             'verify_pressure_separation.py','verify_coefficient_lower_bounds.py',
             'verify_weighted_cutoff.py','check_sharp_endpoint.py']:
    # ed. (2026-10-01): the output directory is passed on.
    subprocess.run([sys.executable,str(root/name),'--output-dir',str(out)],check=True)
print('Every scalar certificate passed.')
