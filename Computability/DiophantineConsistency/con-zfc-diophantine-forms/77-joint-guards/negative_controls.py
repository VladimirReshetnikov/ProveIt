#!/usr/bin/env python3
"""Fail-closed corruption controls for the release manifest, not universal proofs."""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
cases=['joint/joint19_degree88.json','circuits/joint19_degree88_dag.json','guards/determinant26_octic.json','pell/p11_positive_degree257.json','guards/coefficients/beta.bin.gz','incoming/con-zfc-cones-pell-2026-10-23.zip']
with tempfile.TemporaryDirectory(prefix='conzfc-wave11-negative-') as td:
    root=Path(td)/'release';shutil.copytree(ROOT,root,ignore=shutil.ignore_patterns('sources','__pycache__','*.pyc'))
    for name in cases:
        p=root/name;raw=p.read_bytes();p.write_bytes(raw+b'\ncorruption-control\n')
        result=subprocess.run([sys.executable,str(root/'verify.py'),'--manifest-only'],cwd=root,capture_output=True,text=True)
        p.write_bytes(raw)
        if result.returncode==0 or 'Manifest mismatch: '+name not in result.stderr:raise RuntimeError('Corruption not rejected: '+name)
        print('PASS rejected '+name)
print(json.dumps({'status':'PASS','corruption_controls':len(cases),'scope':'Polynomial, fixed payload and archived-input corruption rejection; not semantic completeness.'}))
