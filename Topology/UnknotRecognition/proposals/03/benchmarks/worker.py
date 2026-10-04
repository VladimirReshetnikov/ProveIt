"""One cold-process measurement. Invoked by run.py with a JSON task on stdin."""
from __future__ import annotations
import gc
import json
from pathlib import Path
import sys
from time import perf_counter

ROOT=Path(__file__).resolve().parents[1]
task=json.load(sys.stdin)
original=task['backend'].startswith('original')
sys.path.insert(0,str(ROOT/'baseline' if original else ROOT))
from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot.scan import ScanLimit
from common import sum_family, connected_sum

case=task['case']
if 'sum' in case:
    if case.get('block'):
        block=Diagram.from_json(json.loads((ROOT/'examples'/f"{case['block']}.json").read_text()))
        d=Diagram.from_pd([])
        for _ in range(case['sum']):d=connected_sum(d,block,Diagram)
    else:
        d=sum_family(case['sum'],Diagram)
elif 'json' in case:
    d=Diagram.from_json(case['json'])
else:
    d=Diagram.from_braid(case['strands'],case['word'])
phase=task['phase']
if task['backend']=='original-markowitz':
    from reference_markowitz import reference_rank
if phase=='ordering':
    from fastunknot.scan import best_scan_order,order_profile
gc.collect()
start=perf_counter()
try:
    if phase=='pipeline':
        value=recognize(d,seconds=task['budget']).to_json()
    elif phase=='ordering':
        order=best_scan_order(d.pd,tries=12)
        value={'order':order,'profile':order_profile(d.pd,order)}
    elif task['backend']=='original-markowitz':
        value=reference_rank(d.pd,seconds=task['budget'])
    else:
        options={'seconds':task['budget']}
        if not original:
            options['factor']=phase=='factor'
            options['pivot']='lifo' if task['backend']=='optimized-lifo' else 'markowitz'
        value=khovanov_rank(d.pd,**options)
    elapsed=perf_counter()-start
    status='timeout' if value.get('status')=='UNKNOWN' else 'ok'
except ScanLimit as exc:
    elapsed=perf_counter()-start
    status,value='timeout',{'reason':str(exc)}
except MemoryError:
    elapsed=perf_counter()-start
    status,value='memory',{}
try:
    import resource
    rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
except ImportError:
    rss=None
print(json.dumps({'seconds':elapsed,'status':status,'crossings':d.crossings,
                  'result':value,'peak_rss_native_units':rss}))
