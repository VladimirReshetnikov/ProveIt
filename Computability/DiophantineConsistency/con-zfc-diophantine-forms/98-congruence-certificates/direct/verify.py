#!/usr/bin/env python3
"""Verify the direct package without changing its delivered files."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def require(ok, message):
    if not ok: raise RuntimeError(message)


def main():
    root=Path(__file__).resolve().parent
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    completed=[]
    with tempfile.TemporaryDirectory(prefix='direct2473-') as temp:
        work=Path(temp)/'package'
        shutil.copytree(root,work,ignore=shutil.ignore_patterns('__pycache__'))
        for optimized in (False,True):
            python=[sys.executable,'-B']+(['-O'] if optimized else [])
            output=Path(temp)/('power-opt.json' if optimized else 'power.json')
            tasks=[('symbolic-power', [str(work/'audit_oriented.py'),'--output',str(output)]),
                   ('expanded-quartic',[str(work/'independent_review/check_export.py'),'eq']),
                   ('expanded-small-height',[str(work/'independent_review/check_export.py'),'small_height'])]
            for label,args in tasks:
                r=subprocess.run(python+args,cwd=work,env=env,capture_output=True,text=True)
                require(r.returncode==0,label+' failed: '+r.stderr[-2000:])
                completed.append({'check':label,'optimized':optimized,'status':'PASS'})
        for variant,flags in [('eq',[]),('small_height',['--keep-linear-wires'])]:
            out=Path(temp)/('rebuilt-'+variant)
            r=subprocess.run([sys.executable,'-B',str(work/'build_equation.py'),*flags,'--output',str(out)],
                             cwd=work,env=env,capture_output=True,text=True)
            require(r.returncode==0,'builder failed: '+r.stderr[-2000:])
            for name in ['equation.json','expanded_polynomial.json','BUILD.json']:
                require((out/name).read_bytes()==(root/variant/name).read_bytes(),
                        'byte mismatch '+variant+'/'+name)
            completed.append({'check':'rebuild-'+variant,'status':'PASS'})
        out=Path(temp)/'rebuilt-integer.json'
        r=subprocess.run([sys.executable,'-B',str(work/'build_integer_companion.py'),'--output',str(out)],
                         cwd=work,env=env,capture_output=True,text=True)
        require(r.returncode==0,'integer builder failed')
        require(out.read_bytes()==(root/'integer_companion.json').read_bytes(),'integer lift mismatch')
        completed.append({'check':'rebuild-integer-companion','status':'PASS'})
    print(json.dumps({'status':'PASS','checks':completed,
                      'scope':'Finite algebra, positive-input proof inventory, constructive power fixtures, and deterministic literal rebuilds; not a consistency decision or formal proof replay.'},indent=2))


if __name__=='__main__': main()
