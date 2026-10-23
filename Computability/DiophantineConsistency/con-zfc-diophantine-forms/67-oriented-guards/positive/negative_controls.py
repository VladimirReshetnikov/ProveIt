#!/usr/bin/env python3
"""Run each corruption in a fresh isolated copy, never the delivered packet."""
import json,shutil,subprocess,sys,tempfile
from pathlib import Path
R=Path(__file__).resolve().parent
results=[]
for name in ['changed_circuit_sign','changed_payload_byte','changed_source_pin']:
 with tempfile.TemporaryDirectory(prefix='positive30-') as d:
  dest=Path(d)/'packet';shutil.copytree(R,dest,ignore=shutil.ignore_patterns('__pycache__'))
  if name=='changed_circuit_sign':
   p=dest/'fourteen_positive_degree30.json';x=json.loads(p.read_text());x['source'][1][1]='-';p.write_text(json.dumps(x))
  elif name=='changed_payload_byte':
   p=dest/'coefficients/coefficients/beta.bin.gz';b=bytearray(p.read_bytes());b[-1]^=1;p.write_bytes(b)
  else:
   p=dest/'upstream/ORDINARY_KERNEL.md';p.write_bytes(p.read_bytes()+b'\nCorruption control\n')
  q=subprocess.run([sys.executable,'-O',str(dest/'check.py')],capture_output=True,text=True)
  if not q.returncode:raise RuntimeError('Corruption survived: '+name)
  results.append({'control':name,'rejected':True})
(R/'NEGATIVE_CONTROL_RECEIPT.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
