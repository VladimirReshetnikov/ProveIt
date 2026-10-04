"""Check the supplied 36-crossing input under two distinct scan orders.

Both scans bypass all preprocessing and check d^2 after each crossing. They
share the same cobordism algebra, so this is not an independent full cube at
n=36. The small-instance cube checks are in tests/test_accelerated.py.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from benchmark import worker


def main():
    cases = json.loads((ROOT/'tools/corpus.json').read_text())
    case = next(c for c in cases if c.get('crossings') == 36 and c['method']=='scan')
    out = {'input':case, 'd_squared_checks':True, 'orders':[]}
    dest = ROOT/'results/hard-case-verification.json'
    for name, order in [('greedy', None), ('natural', list(range(36)))]:
        job = {'engine':'optimized', 'method':'scan', 'diagram':case['diagram'],
               'order':order, 'check_d_squared':True, 'limit':90, 'repeats':1}
        result = worker(job)
        out['orders'].append({'engine':'optimized', 'order_name':name, **result})
        dest.write_text(json.dumps(out,indent=2)+'\n')
        print(name, result['status'], result['median_seconds'], flush=True)
    completed = [r['answer'] for r in out['orders'] if r['status']=='ok']
    assert len(completed) == 2
    assert all(r['reduced_rank']==2949 for r in completed)
    assert completed[0]['by_degree'] == completed[1]['by_degree']

if __name__ == '__main__':
    main()
