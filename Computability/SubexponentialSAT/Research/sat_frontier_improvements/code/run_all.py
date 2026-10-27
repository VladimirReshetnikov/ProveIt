#!/usr/bin/env python3
"""Reproduce exact checks offline using only the standard library."""
import json
import subprocess
import sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
out=root/'reproduced';out.mkdir(exist_ok=True)
summary=[]
for optimized in (False,True):
    suffix='_optimized' if optimized else ''
    prefix=[sys.executable]+(['-O'] if optimized else [])
    tasks=[('kernel',[str(root/'code/verify_kernel.py'),str(root/'vendor/joint_cauchy.py')]),
           ('variable_arity',[str(root/'code/verify_variable_arity.py'),str(out/('variable_arity'+suffix+'.json'))]),
           ('cache_composition',[str(root/'code/check_cache_composition.py')])]
    extra=root/'code/verify_degree_corollaries.py'
    if extra.exists(): tasks.append(('degree_corollaries',[str(extra)]))
    for name,args in tasks:
        result=subprocess.run(prefix+args,cwd=root,text=True,capture_output=True,check=True)
        data=json.loads(result.stdout)
        if str(data.get('status','')).lower() not in ('pass','passed'):
            raise RuntimeError(f'{name}: missing passing status')
        (out/(name+suffix+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        summary.append({'check':name,'optimized':optimized,'status':'PASS'})
        print(name,suffix or 'normal','PASS',flush=True)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('All exact checks passed. This is not an end-to-end SAT verification.')
