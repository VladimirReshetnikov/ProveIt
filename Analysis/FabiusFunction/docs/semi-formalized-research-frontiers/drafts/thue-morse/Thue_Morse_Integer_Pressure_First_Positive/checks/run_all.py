from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
(root.parent/'data').mkdir(exist_ok=True)
for script in ['check_second_response.py','check_orbit_coefficients.py','check_large_orders.py','check_finite_basis.py','check_finite_formula.py']:
 r=subprocess.run([sys.executable,str(root/script)],capture_output=True,text=True)
 (root.parent/'data'/(Path(script).stem+'.log')).write_text(r.stdout+r.stderr)
 if r.returncode:
  print(r.stdout+r.stderr);raise SystemExit(r.returncode)
 print(script+': passed')
