#!/usr/bin/env python3
"""Fresh-process timing worker. The parent supplies only trusted local fixtures."""
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
job=json.loads(sys.argv[1])
sys.path.insert(0,str(ROOT/('baseline/fast' if job['version']=='baseline' else 'fast')))
from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.scan import ScanLimit
try:
    import resource
except ImportError:
    resource=None

d=Diagram.from_json(job['input'])
kwargs=job.get('kwargs',{}).copy()
kwargs['seconds']=job['seconds']
start=time.perf_counter()
try:
    if job['mode']=='rank':
        r=khovanov_rank(d.pd,**kwargs)
        result={'status':'EXACT','reduced_rank':r['reduced_rank'],
                'by_degree':r['by_degree'],'stats':r['stats']}
    else:
        r=recognize(d,**kwargs)
        result={'status':r.status,'method':r.method,'evidence':r.evidence}
except (ScanLimit,MemoryError) as exc:
    result={'status':'UNKNOWN','reason':str(exc)}
result['seconds']=time.perf_counter()-start
result['crossings']=d.crossings
result['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss if resource else None
print(json.dumps(result,sort_keys=True),flush=True)
