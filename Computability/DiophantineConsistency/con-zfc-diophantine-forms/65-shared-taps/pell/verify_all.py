#!/usr/bin/env python3
"""Run the complete component in a temporary copy and verify deterministic output."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent

def require(ok,label):
    if not ok: raise ValueError(label)

def main():
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    for rec in pins['files']:
        raw=(HERE/rec['local']).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==rec['sha256'],'source SHA256: '+rec['local'])
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob==rec['git_blob_sha1'],'source git blob: '+rec['local'])
    compared=['circuits/p14_degree26.json','circuits/p14_degree30.json','METRICS.json']
    expected={f:(HERE/f).read_bytes() for f in compared}
    stages=[]
    with tempfile.TemporaryDirectory(prefix='conzfc_pell14_') as temporary:
        work=Path(temporary)/'component'
        shutil.copytree(HERE,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        mode=['-O'] if sys.flags.optimize else []
        for script in ['coefficients/build_coefficients.py','coefficients/audit_coefficients.py','build.py','independent_check.py']:
            result=subprocess.run([sys.executable,*mode,str(work/script)],cwd=work,
                                  stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            if result.returncode:
                raise RuntimeError(script+'\n'+result.stdout+'\n'+result.stderr)
            stages.append({'script':script,'status':'PASS'})
        for f,raw in expected.items():require((work/f).read_bytes()==raw,'byte-identical rebuild: '+f)
        results=json.loads((work/'CHECK_RESULTS.json').read_text())
    print(json.dumps({'status':'PASS','source_files':len(pins['files']),
      'byte_identical_rebuilds':compared,'stages':stages,'component_checks':results,
      'assertions_disabled':bool(sys.flags.optimize)},indent=2))

if __name__=='__main__':main()
