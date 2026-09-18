"""One isolated timed job, excluding process startup and initial input parsing."""
from __future__ import annotations
import importlib
import json
import platform
import sys
import time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / 'reference')]

def main():
    job = json.load(sys.stdin)
    package = 'baseline_fastunknot' if job['engine'] == 'baseline' else 'fastunknot'
    mod = importlib.import_module(package)
    diagram = mod.Diagram.from_json(job['input'])
    start = time.perf_counter()
    kind = job.get('kind', 'rank')
    if kind == 'rank':
        try:
            result = mod.khovanov_rank(diagram.pd, seconds=job.get('seconds', 20))
        except mod.ScanLimit as exc:
            result = {'status': 'UNKNOWN', 'reason': str(exc)}
    elif kind == 'recognize':
        result = mod.recognize(diagram, seconds=job.get('seconds', 20),
                               **job.get('options', {})).to_json()
    elif kind == 'ordering':
        scan = importlib.import_module(package + '.scan')
        order = scan.best_scan_order(diagram.pd, tries=12)
        result = {'profile': scan.order_profile(diagram.pd, order)}
    elif kind == 'descending':
        simplify = importlib.import_module(package + '.simplify')
        result = {'dart': simplify.descending_start(diagram)}
    else:
        raise ValueError(kind)
    elapsed = time.perf_counter() - start
    try:
        import resource
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    except ImportError:
        rss = None
    print(json.dumps({'elapsed': elapsed, 'peak_rss_native': rss, 'result': result}))

if __name__ == '__main__':
    main()
