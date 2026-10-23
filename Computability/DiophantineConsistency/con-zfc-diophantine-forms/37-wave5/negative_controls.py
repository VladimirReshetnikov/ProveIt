#!/usr/bin/env python3
"""Reject altered payload, altered circuit, and missing dependency in disposable copies."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json,shutil
from verify import validate
P=Path(__file__).resolve().parent

def main():
 cases=[('changed_coefficient','coefficients/coefficients_compact/MC.bin','flip'),('changed_circuit','signed/generated/signed14.json','flip'),('missing_dependency','nine/source/30-quartic31/nine/nu31/COMPACT_CONSTANTS.json','remove')]
 result=[]
 for name,rel,mode in cases:
  with TemporaryDirectory(prefix='conzfc-negative-') as t:
   Q=Path(t)/'package';shutil.copytree(P,Q,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
   validate(Q);f=Q/rel
   if mode=='remove':f.unlink()
   else:
    raw=bytearray(f.read_bytes());raw[len(raw)//2]^=1;f.write_bytes(raw)
   try:validate(Q)
   except (AssertionError,FileNotFoundError) as e:result.append({'case':name,'status':'REJECTED','reason':str(e)})
   else:raise AssertionError('Corruption accepted: '+name)
 out={'status':'PASS','controls':result,'scope':'Seal and binding rejection tests, not mathematical soundness certificates.'}
 (P/'NEGATIVE_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
