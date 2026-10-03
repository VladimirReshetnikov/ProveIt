#!/usr/bin/env python3
from pathlib import Path
import subprocess
import sys

here=Path(__file__).resolve().parent
for name in ['generate_determinant.py','independent_replay.py','check_supports.py']:
    subprocess.run([sys.executable,'-O',str(here/name)],check=True)
print('All exact certificate reconstructions and finite support regressions passed.')
