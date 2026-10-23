#!/usr/bin/env python3
"""Three release-integrity corruption controls, distinct from semantic tests."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,shutil,tempfile
import verify
ROOT=Path(__file__).resolve().parent
TARGETS=['weights/code_v1.json','packing/mask_popcount/generated/signed10_b2.json','batching/coefficients/MC.bin.gz']
results=[]
for target in TARGETS:
 with tempfile.TemporaryDirectory(prefix='proveit-integrity-control-') as td:
  work=Path(td)/'release';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  p=work/target;b=bytearray(p.read_bytes());b[len(b)//2]^=1;p.write_bytes(b)
  try:verify.authenticate(work)
  except ValueError:results.append({'target':target,'result':'rejected'})
  else:raise RuntimeError('Corruption escaped authentication: '+target)
print(json.dumps({'status':'PASS','controls':results,'scope':'Byte-integrity controls only; selective semantic mutation tests are separate.'},indent=2))
