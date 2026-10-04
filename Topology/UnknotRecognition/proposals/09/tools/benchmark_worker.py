"""One isolated benchmark job. Invoked by benchmark.py, not normally by users."""
import gc
import importlib
import json
import statistics
import sys
import time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))


def main():
    request=json.loads(sys.stdin.read())
    package='baseline_fastunknot' if request['implementation']=='baseline' else 'fastunknot'
    module=importlib.import_module(package)
    scan=importlib.import_module(package+'.scan')
    diagram=module.Diagram.from_json(request['input'])
    times=[]
    result=None
    for repeat in range(request['repetitions']):
        for name in ('circles','glue'):
            getattr(scan,name).cache_clear()
        if hasattr(scan,'clear_scan_caches'):
            scan.clear_scan_caches()
        gc.collect()
        start=time.perf_counter()
        try:
            if request['task']=='pipeline':
                r=module.recognize(diagram,seconds=request['seconds'],max_objects=request['max_objects'])
                result={'status':r.status,'method':r.method,'evidence':r.evidence}
            elif request['task']=='order':
                r=scan.best_scan_order(diagram.pd,tries=min(diagram.crossings,12))
                result={'status':'DONE','max_boundary':scan.order_profile(diagram.pd,r)[0]}
            else:
                options=dict(seconds=request['seconds'],max_objects=request['max_objects'])
                if request['implementation']=='accelerated-no-factors':
                    options['factor']=False
                r=scan.khovanov_rank(diagram.pd,**options)
                result={'status':'DONE','rank':r['rank'],'reduced_rank':r['reduced_rank'],
                        'by_degree':r['by_degree'],'stats':r['stats']}
        except (scan.ScanLimit,MemoryError) as exc:
            result={'status':'UNKNOWN','reason':str(exc)}
        times.append(time.perf_counter()-start)
        if result['status']=='UNKNOWN':
            break
    print(json.dumps({'samples_seconds':times,'median_seconds':statistics.median(times),
                      'result':result}))

if __name__=='__main__':
    main()
