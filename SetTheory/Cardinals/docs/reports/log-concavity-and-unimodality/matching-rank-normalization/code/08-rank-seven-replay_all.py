#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
subprocess.run([sys.executable,'-O',str(root/'verify_middle.py')],check=True)
print('All exact sectors and auxiliary inequalities passed.')
