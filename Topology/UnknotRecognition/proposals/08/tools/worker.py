"""One cold benchmark invocation; JSON input on stdin and JSON result on stdout."""
from __future__ import annotations
import json
from pathlib import Path
import sys
from time import perf_counter
ROOT = Path(__file__).resolve().parents[1]
request = json.load(sys.stdin)
implementation = request['implementation']
sys.path.insert(0, str(ROOT / 'baseline' if implementation == 'baseline' else ROOT))
from fastunknot import Diagram, ScanLimit, khovanov_rank, recognize
from fastunknot.scan import best_scan_order
from fastunknot.simplify import descending_start
# Loading and validation are deliberately excluded from kernel timings.
d = Diagram.from_json(request['diagram'])
mode = request['mode']
kwargs = {}
if request.get('order') == 'input':
    kwargs['order'] = list(range(d.crossings))
elif request.get('order') == 'reverse':
    kwargs['order'] = list(reversed(range(d.crossings)))
if implementation != 'baseline' and mode == 'scan':
    kwargs['factor'] = False
if request.get('check_d2'):
    kwargs['check_d_squared'] = True
if mode in ('scan', 'rank') and request.get('seconds') is not None:
    kwargs['seconds'] = request['seconds']
if request.get('max_objects') is not None:
    kwargs['max_objects'] = request['max_objects']
start = perf_counter()
try:
    if mode in ('scan', 'rank'):
        value = khovanov_rank(d.pd, **kwargs)
    elif mode == 'pipeline':
        value = recognize(d, **kwargs).to_json()
    elif mode == 'order':
        value = best_scan_order(d.pd, tries=min(d.crossings, 12))
    elif mode == 'descending':
        value = descending_start(d)
    else:
        raise ValueError('unknown benchmark mode')
    result = {'completed': True, 'seconds': perf_counter() - start,
              'result': value, 'implementation': implementation, 'mode': mode}
except (ScanLimit, MemoryError) as exc:
    result = {'completed': False, 'seconds': perf_counter() - start,
              'reason': str(exc), 'implementation': implementation, 'mode': mode}
try:
    import resource
    result['max_rss_kib_linux'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
except ImportError:
    pass
print(json.dumps(result))
