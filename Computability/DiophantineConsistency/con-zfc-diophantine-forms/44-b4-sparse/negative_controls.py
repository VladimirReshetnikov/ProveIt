#!/usr/bin/env python3
"""Three release-integrity corruption controls; not semantic proof tests."""
import json,shutil,tempfile,sys
sys.dont_write_bytecode = True
from pathlib import Path
from verify import authenticate
ROOT=Path(__file__).resolve().parent
CASES=['root_checks/bose_chowla_31_optimized.json','native/coefficients/MC.bin.gz','sun/generated/sun_b4.json']
def main():
 results=[]
 for name in CASES:
  with tempfile.TemporaryDirectory(prefix='proveit-negative-') as tmp:
   r=Path(tmp)/'release';shutil.copytree(ROOT,r,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
   p=r/name;body=bytearray(p.read_bytes());body[len(body)//2]^=1;p.write_bytes(body)
   try:authenticate(r)
   except ValueError as e:
    if name not in str(e):raise
    results.append({'changed_file':name,'rejected':True})
   else:raise AssertionError('Corruption accepted: '+name)
 print(json.dumps({'status':'PASS','controls':results,'scope':'Byte-integrity rejection only; unbounded mathematical correctness comes from proofs.'},indent=2))
if __name__=='__main__':main()
