#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
names=['primary/verify_real_counterexample.py','primary/check_generic_six_profiles.py','primary/check_top_coupled_five.py','primary/check_top_coupled_six.py','independent/replay.py','independent/replay_coupled.py']
for name in names:
 cmd=[sys.executable,'-O',str(here/name)]
 if name.startswith('independent/') and '--save-certificate' in sys.argv:cmd.append('--save-certificate')
 p=subprocess.run(cmd,text=True,capture_output=True)
 print(p.stdout,end='',flush=True)
 if p.returncode:raise RuntimeError((name,p.returncode,p.stderr))
print('ALL PRIMARY AND INDEPENDENT EXACT REPLAYS PASS')
