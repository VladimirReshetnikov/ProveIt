#!/usr/bin/env python3
"""Convenience driver: exact checks by default; --all includes both numerical runs."""
import argparse,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--all',action='store_true');args=p.parse_args()
subprocess.run([sys.executable,str(root/'code/verify_exact.py')],check=True,cwd=root)
if args.all:
    for dps in (45,60):
        subprocess.run([sys.executable,str(root/'code/verify_numeric.py'),'--dps',str(dps)],check=True,cwd=root)
