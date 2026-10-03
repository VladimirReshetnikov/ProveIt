"""Recompute the rational matrix identities; requires SymPy."""
from pathlib import Path
import subprocess,sys
# ed. (2026-10-01): the recomputations now write to <output-dir>, by
# default data/rerun/, with LF line endings (as delivered they overwrote the
# recorded files in data/, with CRLF on Windows). Pass --output-dir data on a
# copy to regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser()
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data'/'rerun')
out=_ed.parse_known_args()[0].output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
ROOT=Path(__file__).resolve().parents[1]
# ed. (2026-10-01): the output directory is passed on. run_all.py then checks the
# recorded Schur and identity files in data/; compare them with the recomputed ones.
subprocess.run([sys.executable,str(ROOT/'code/check_schur.py')]+list(map(str,range(2,15)))+['--output-dir',str(out)],check=True)
subprocess.run([sys.executable,str(ROOT/'code/check_fixed_offset.py'),'--output-dir',str(out)],check=True)
subprocess.run([sys.executable,str(ROOT/'code/run_all.py'),'--output-dir',str(out)],check=True)
print('All rational matrix computations reproduced')
