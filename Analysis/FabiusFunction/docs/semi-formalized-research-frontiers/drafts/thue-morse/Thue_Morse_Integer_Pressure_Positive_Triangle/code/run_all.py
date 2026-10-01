from pathlib import Path
import subprocess,sys
# ed. (2026-10-01): the checkers now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
root=Path(__file__).resolve().parent
for name in ['check_triangle.py','check_basis_signs.py','check_m2_cubic.py']:
    # ed. (2026-10-01): the output directory is passed on.
    subprocess.run([sys.executable,str(root/name),'--output-dir',str(out)],check=True)
print('All exact checks passed')
