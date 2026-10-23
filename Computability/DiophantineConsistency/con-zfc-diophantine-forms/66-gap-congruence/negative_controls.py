#!/usr/bin/env python3
"""Separate byte-integrity corruption from mathematical certificate mutations."""
from pathlib import Path
import tempfile,shutil,subprocess,sys,json
R=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as t:
 p=Path(t)/'release';shutil.copytree(R,p)
 q=p/'source/parent_source.json';q.write_bytes(q.read_bytes()+b' ')
 out=subprocess.run([sys.executable,str(p/'verify.py')],capture_output=True,text=True)
 if out.returncode==0 or 'manifest source/parent_source.json' not in out.stderr:raise ValueError('byte-tamper control')
 print('PASS sealed-manifest byte-tamper control (not a mathematical test)')
r=subprocess.run([sys.executable,str(R/'carry/test_certificates.py')],cwd=R)
if r.returncode:raise RuntimeError('coherent-hash mathematical mutation controls')
print('PASS coherent-hash source/packing mutation controls')

r=subprocess.run([sys.executable,str(R/'integer/negative_controls.py')],cwd=R)
if r.returncode:raise RuntimeError('integer semantic mutation controls')
print('PASS integer target, threshold and mask mutation controls')
