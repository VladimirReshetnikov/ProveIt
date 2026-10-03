from pathlib import Path
import subprocess,sys
# ed. (2026-10-01): the two checkers and their console logs now write to
# <output-dir>, by default rerun/ beside this program, with LF line endings
# (as delivered the logs were written beside this program, and the checkers
# overwrote their recorded JSON beside themselves, with CRLF on Windows).
# Pass --output-dir with this program's own directory, on a copy, to
# regenerate the recorded files.
import argparse
_ed=argparse.ArgumentParser(description='Run both exact checkers.')
_ed.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'rerun')
out=_ed.parse_args().output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
p=Path(__file__).resolve().parent
for name in ['verify_modulo.py','check_slices.py']:
 # ed. (2026-10-01): the output directory is passed on, and each log is written there with LF.
 r=subprocess.run([sys.executable,str(p/name),'--output-dir',str(out)],capture_output=True,text=True)
 (out/(Path(name).stem+'.log')).write_bytes((r.stdout+r.stderr).encode('utf-8'))
 if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
 print(name+': passed')
