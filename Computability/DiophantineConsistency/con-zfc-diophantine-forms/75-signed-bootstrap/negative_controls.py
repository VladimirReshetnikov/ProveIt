#!/usr/bin/env python3
"""Three fail-closed integrity controls; does not test universal mathematics."""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile
R=Path(__file__).resolve().parent
cases=['guards/signed34_sextic.json','low_degree/p13_degree30.json','incoming/ConZFC_Gap_Congruence_2026-10-23.zip']
with tempfile.TemporaryDirectory(prefix='conzfc-wave10-negative-') as td:
 root=Path(td)/'release';shutil.copytree(R,root,ignore=shutil.ignore_patterns('sources','__pycache__','*.pyc'))
 for name in cases:
  p=root/name;raw=p.read_bytes();p.write_bytes(raw+b'\ncorruption-control\n')
  result=subprocess.run([sys.executable,str(root/'verify.py'),'--manifest-only'],cwd=root,capture_output=True,text=True)
  p.write_bytes(raw)
  if result.returncode==0 or 'Manifest mismatch: '+name not in result.stderr:raise RuntimeError('Corruption was not rejected: '+name)
  print('PASS rejected '+name)
print(json.dumps({'status':'PASS','integrity_corruption_controls':len(cases),'scope':'Manifest corruption rejection, not semantic completeness.'}))
