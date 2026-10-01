#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
names=['primary/check_hyperplane_transition.py','independent/check_transition.py','independent/replay_hyperplane.py','independent/check_minor_supports.py']
for name in names:
 cmd=[sys.executable,'-O',str(here/name)]
 if '--save-certificate' in sys.argv and name.startswith('independent/'):cmd.append('--save-certificate')
 p=subprocess.run(cmd,text=True,capture_output=True)
 print(p.stdout,end='',flush=True)
 if p.returncode:raise RuntimeError((name,p.returncode,p.stderr))
print('ALL PRIMARY AND TWO INDEPENDENT EXACT REPLAYS PASS')
