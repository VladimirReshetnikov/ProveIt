#!/usr/bin/env python3
"""Cross-check the large case after certified decreasing Reidemeister moves.

This is validation rather than a benchmark: a changed diagram has a potentially
shifted cube degree. All degree dimensions are compared after subtracting the
number of negative crossings. Retain UNKNOWN results honestly.
"""
import json
from pathlib import Path
import subprocess
import sys
import os
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.simplify import simplify
fixtures=json.loads((ROOT/'results/fixtures.json').read_text())
case=next(c for c in fixtures if c['id']=='rank/random_5_36')
d=Diagram.from_json(case['input']);reduced,trace=simplify(d)
out={'original_crossings':d.crossings,'simplified_crossings':reduced.crossings,
     'original_negative_crossings':d.signs().count(-1),
     'simplified_negative_crossings':reduced.signs().count(-1),
     'pd':reduced.to_json(),'reidemeister_trace':[m.to_json() for m in trace],'runs':[]}
for version in ('baseline','optimized'):
    job={'input':reduced.to_json(),'mode':'rank','seconds':30,
         'version':version,'kwargs':{}}
    try:
        p=subprocess.run([sys.executable,str(ROOT/'tools/benchmark_worker.py'),json.dumps(job)],
                         capture_output=True,text=True,timeout=35,
                         env={**os.environ,'PYTHONHASHSEED':'0'})
        r=json.loads(p.stdout) if p.returncode==0 else {'status':'ERROR','stderr':p.stderr}
    except subprocess.TimeoutExpired:r={'status':'HARD_TIMEOUT','process_limit_seconds':35}
    r['version']=version;out['runs'].append(r)
    (ROOT/'results/stress_validation.json').write_text(json.dumps(out,indent=2)+'\n')
    print(version,r['status'],r.get('reduced_rank'),r.get('seconds'),flush=True)
bench=json.loads((ROOT/'results/benchmarks.json').read_text())
raw=next(x for x in bench['observations'] if x['case']==case['id'] and x['status']=='EXACT')
norm={int(h)-out['original_negative_crossings']:c for h,c in raw['by_degree'].items()}
for r in out['runs']:
    if r['status']=='EXACT':
        got={int(h)-out['simplified_negative_crossings']:c for h,c in r['by_degree'].items()}
        if norm!=got:raise AssertionError('normalized degree mismatch')
out['completed_normalized_degree_comparisons_agree']=True
(ROOT/'results/stress_validation.json').write_text(json.dumps(out,indent=2)+'\n')
