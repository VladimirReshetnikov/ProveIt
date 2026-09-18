"""Cross-check the supplied raw stress case against its R2-reduced diagram.

This is an invariance check of the same backend, not an independent large
Khovanov computation. Independent dense-cube tests are in tests/.
"""
from __future__ import annotations
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from time import perf_counter
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram, khovanov_rank
from fastunknot.scan import clear_caches
from fastunknot.simplify import simplify
from fastunknot.alexander import alexander_polynomial, evaluate

def main():
    original=Diagram.from_json(json.loads((ROOT/'benchmarks/inputs/five_braid_36.json').read_text()))
    reduced,trace=simplify(original)
    assert all(move.kind=='R2' for move in trace)
    samples=[]
    for name,diagram in (('original',original),('R2-reduced',reduced)):
        clear_caches();start=perf_counter()
        result=khovanov_rank(diagram.pd,seconds=30,check_d_squared=True)
        samples.append({'diagram':name,'crossings':diagram.crossings,
                        'wall_seconds':perf_counter()-start,'result':result})
    r0,r1=(s['result'] for s in samples)
    assert r0['reduced_rank']==r1['reduced_rank']==2949
    assert r0['by_degree']=={h+len(trace):v for h,v in r1['by_degree'].items()}
    alex=alexander_polynomial(reduced)
    data={'generated_utc':datetime.now(timezone.utc).isoformat(),
          'trace':[m.to_json() for m in trace], 'samples':samples,
          'alexander_coefficients':alex,'determinant':abs(evaluate(alex,-1)),
          'checks':'same rank; cube-degree shift of one per R2; d^2=0 after every scan stage',
          'caution':'determinant agreement is a cross-check, not a general rank formula'}
    (ROOT/'benchmarks/stress_validation.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Stress validation passed: reduced rank 2949 before/after six R2 moves.')
if __name__=='__main__':main()
