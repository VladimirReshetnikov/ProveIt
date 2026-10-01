from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for name in ['verify_modulo.py','check_slices.py']:
 r=subprocess.run([sys.executable,str(p/name)],capture_output=True,text=True)
 (p/(Path(name).stem+'.log')).write_text(r.stdout+r.stderr)
 if r.returncode:print(r.stdout+r.stderr);raise SystemExit(r.returncode)
 print(name+': passed')
