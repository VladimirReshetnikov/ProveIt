"""Descriptive scaling experiment; not an interval-certified timing experiment."""
from __future__ import annotations
import csv,json,math,platform,statistics,sys
from fractions import Fraction as Q
from pathlib import Path
from time import perf_counter
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
from fourier_tv import ProductPair,relative_fast

def binomial_tv(n,p):
    # Summing the exact binomial reduction with 80-decimal arithmetic; this is
    # a high-precision reference, not an outward-rounded interval certificate.
    mp.mp.dps=80
    p=mp.mpf(p.numerator)/p.denominator
    a=(1-p)**n;b=mp.mpf(2)**(-n)
    result=abs(a-b)
    for k in range(n):
        ratio=mp.mpf(n-k)/(k+1)
        a*=ratio*p/(1-p);b*=ratio
        result+=abs(a-b)
    return float(result/2)

def main():
    rows=[]
    for n in [10,100,1000,5000,10000]:
        bias=Q(round(0.4*10**8/math.sqrt(n)),10**8)
        p=Q(1,2)+bias
        pair=ProductPair.create([[p,1-p]]*n,[[Q(1,2)]*2]*n)
        times=[]
        for repeat in range(3):
            start=perf_counter();result=relative_fast(pair,0.1);times.append(perf_counter()-start)
        reference=binomial_tv(n,p)
        row=dict(n=n,input_entries=2*n,bias=str(bias),nodes=result['nodes'],
                 median_seconds=statistics.median(times),reference_tv=reference,
                 estimate=result['estimate'],relative_error=abs(result['estimate']-reference)/reference,
                 seconds_per_coordinate=statistics.median(times)/n)
        rows.append(row);print(row,flush=True)
    with (ROOT/'data'/'scaling.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    (ROOT/'data'/'environment.json').write_text(json.dumps(dict(python=sys.version,
       numpy=np.__version__,mpmath=mp.__version__,platform=platform.platform(),
       timing_repetitions=3,timing_summary='median wall time; hardware-dependent',
       seed=20261008),indent=2))
if __name__=='__main__':main()
