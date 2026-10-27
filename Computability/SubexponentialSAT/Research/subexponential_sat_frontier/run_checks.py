#!/usr/bin/env python3
"""Run delivered checkers in both modes without changing recorded evidence."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
CODE=ROOT/'code'
OUT=ROOT/'replay_results'
OUT.mkdir(exist_ok=True)
reference=CODE/'reference_balanced_packing.py'
expected='5e899df4fd25b1371fe6f42c13f87caba49637fb92da0f12b12dd01a831bb6d2'
if hashlib.sha256(reference.read_bytes()).hexdigest()!=expected:
    raise SystemExit('Reference implementation hash mismatch')
scripts=['verify_heterogeneous_schedule.py','verify_cached_schedule.py',
         'verify_cached_balancing.py','verify_precision_peeling.py']
summary={'status':'pass','reference_sha256':expected,'checks':[]}
for name in scripts:
    records=[]
    for optimized in (False,True):
        before=time.perf_counter()
        cmd=[sys.executable]+(['-O'] if optimized else [])+[str(CODE/name)]
        result=subprocess.run(cmd,cwd=ROOT,capture_output=True,text=True,check=True)
        parsed=json.loads(result.stdout)
        if parsed.get('status') not in ('pass','passed'):
            raise RuntimeError(f'{name} did not report success')
        suffix='_optimized' if optimized else ''
        (OUT/(Path(name).stem+suffix+'.json')).write_text(
            json.dumps(parsed,indent=2,sort_keys=True)+'\n')
        records.append(parsed)
        summary['checks'].append({'script':name,'optimized':optimized,
                                  'seconds':time.perf_counter()-before})
    if records[0]!=records[1]:
        raise RuntimeError(f'normal and optimized results differ: {name}')
    print(name+': both modes passed; identical mathematical results')
summary['normal_optimized_equivalence']=True
(OUT/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('All four checkers passed. Results: replay_results/verification_summary.json')
