"""Fresh-process worker; imports and input construction are outside timing."""
import argparse, json, sys, time, types, heapq
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

def main():
    p=argparse.ArgumentParser()
    p.add_argument('backend', choices=['baseline','optimized','cached-lifo','old-algebra-fill'])
    p.add_argument('mode', choices=['scan','pipeline','factored','forced-scan-pipeline','order'])
    p.add_argument('file');p.add_argument('--cap',type=float,default=20)
    p.add_argument('--check-d2',action='store_true');args=p.parse_args()
    if args.backend in ('baseline','old-algebra-fill'):
        from baseline import fastunknot as lib
        from baseline.fastunknot import scan
    else:
        import fastunknot as lib
        from fastunknot import scan
    if args.backend=='old-algebra-fill':
        from fastunknot.scan import ScanComplex as NewComplex
        # Only the cancellation-loop implementation changes. Use the baseline's
        # original uncached compose/inverse functions, not the optimized algebra.
        namespace=dict(scan.__dict__,heappush=heapq.heappush,heappop=heapq.heappop)
        scan.ScanComplex.eliminate=types.FunctionType(NewComplex.eliminate.__code__,namespace)
        scan.ScanComplex.pivot_strategy='fill'
    with open(args.file,encoding='utf8') as f: data=json.load(f)
    d=lib.Diagram.from_json(data)
    start=time.perf_counter();status='OK'
    try:
        if args.mode=='scan':
            kw=dict(seconds=args.cap,check_d_squared=args.check_d2)
            if args.backend in ('optimized','cached-lifo'):
                kw['pivot_strategy']='lifo' if args.backend=='cached-lifo' else 'fill'
            answer=lib.khovanov_rank(d.pd,**kw)
        elif args.mode in ('pipeline','forced-scan-pipeline'):
            kw=dict(seconds=args.cap)
            if args.mode=='forced-scan-pipeline':
                kw['use_alexander']=False
                if args.backend=='optimized':kw['use_jones']=False
            answer=lib.recognize(d,**kw).to_json()
            if answer['status']=='UNKNOWN':status='LIMIT'
        elif args.mode=='order':
            answer={'order':scan.best_scan_order(d.pd,tries=min(d.crossings,12))}
        else:
            from fastunknot.factor import factorized_khovanov_rank
            answer=factorized_khovanov_rank(d,seconds=args.cap)
    except (scan.ScanLimit,MemoryError) as exc:
        answer={'reason':str(exc)};status='LIMIT'
    elapsed=time.perf_counter()-start;memory=None
    try:
        import resource
        memory=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        if sys.platform=='darwin':memory//=1024
    except ImportError:pass
    print(json.dumps({'backend':args.backend,'mode':args.mode,'status':status,
        'seconds':elapsed,'peak_process_rss_KiB':memory,'answer':answer}))

if __name__=='__main__':main()
