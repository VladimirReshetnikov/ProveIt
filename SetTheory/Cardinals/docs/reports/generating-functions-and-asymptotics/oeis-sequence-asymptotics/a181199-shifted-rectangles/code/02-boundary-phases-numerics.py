"""High-precision diagnostics; decimal values are not interval certificates."""
from __future__ import annotations
import csv, gc, json, time
from math import factorial, prod
from pathlib import Path
import mpmath as mp
from tableaux import count, rare_core
ROOT=Path(__file__).resolve().parents[1]

def main():
    mp.mp.dps=70; rows=[];t0=time.perf_counter()
    for m in (3,4,5):
        r=m-2; d=r*(r-1)//2; J=prod(factorial(j) for j in range(r))
        L=mp.sqrt(mp.mpf(m)/2)*(2*mp.pi)**(-mp.mpf(r)/2)*mp.mpf(4)**(-d)*mp.mpf(9)**(-r)*J
        b=[mp.mpf(a.split('/')[0])/mp.mpf(a.split('/')[1]) if '/' in a else mp.mpf(a)
           for a in json.loads((ROOT/f'data/coefficients_m{m}.json').read_text())['b']]
        for n in (10,20,40,60):
            R=count(m,n,True); H=rare_core(m,n);gc.collect()
            leading=L*(mp.mpf(m)**m/4)**n/mp.mpf(n)**(mp.mpf(r*r)/2)
            row={'m':m,'n':n,'R':str(R),'H':str(H),'R_over_leading':mp.nstr(mp.mpf(R)/leading,25),
                 'H_over_R':mp.nstr(mp.mpf(H)/R,25)}
            for k in range(4):
                approximate=leading*sum(b[j]/mp.mpf(n)**j for j in range(k+1))
                row[f'error_order_{k}']=mp.nstr(approximate/R-1,25)
            rows.append(row)
            print(m,n,'ratio',row['R_over_leading'],'errors',*(row[f'error_order_{k}'] for k in range(4)),flush=True)
    with (ROOT/'data/numerics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    (ROOT/'data/numerics.json').write_text(json.dumps({'precision_digits':mp.mp.dps,'seconds':time.perf_counter()-t0,
        'status':'Decimal diagnostics, not rigorous interval enclosures','rows':rows},indent=2)+'\n')
if __name__=='__main__':main()
