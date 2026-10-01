#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json
here=Path(__file__).resolve().parent
for name in ('verify_plane_profiles.py','check_four_quotient_unit.py','verify_five_by_three.py'):
 p=subprocess.run([sys.executable,'-O',str(here/name)],text=True,capture_output=True)
 print(p.stdout,end='')
 if p.returncode:raise RuntimeError((name,p.stderr,p.returncode))
 if name=='verify_plane_profiles.py':
  want=json.loads((here.parent/'data'/'verify_plane_profiles.json').read_text())
  if json.loads(p.stdout)!=want:raise RuntimeError('plane certificate summary mismatch')
 if name=='check_four_quotient_unit.py':
  want=json.loads((here.parent/'data'/'check_four_quotient_unit.json').read_text())
  if json.loads(p.stdout)!=want:raise RuntimeError('baseline diagnostic summary mismatch')
print('ALL EXACT REPLAYS PASS')
