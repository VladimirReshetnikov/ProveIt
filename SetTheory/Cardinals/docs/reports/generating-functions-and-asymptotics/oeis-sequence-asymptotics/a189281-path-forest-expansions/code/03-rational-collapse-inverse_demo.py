#!/usr/bin/env python3
"""Optional, non-certified index reconstruction diagnostics (requires mpmath)."""
from pathlib import Path
import json
try:
    import mpmath as mp
except ImportError as exc:
    raise SystemExit('The optional inverse diagnostic requires mpmath.') from exc


def reconstruct(value: int, r: int = 2, s: int = 2):
    if value <= 0 or min(r,s) < 1:
        raise ValueError('Use a positive value and positive offsets.')
    T = mp.log(value)+1-mp.log(2*mp.pi)/2
    if T <= 0:
        raise ValueError('This asymptotic formula requires a sufficiently large value.')
    z = T/mp.lambertw(T/mp.e)
    estimate = (z-mp.mpf(1)/2+(mp.mpf(1)/24-(r+s-1))/(z*mp.log(z))
                +(r-1)*(s-1)/(z*z*mp.log(z)))
    return z, estimate


def main() -> None:
    mp.mp.dps = 60
    out = Path(__file__).resolve().parents[1]/'data'
    values = {}
    for line in (out/'b189281_0_30.txt').read_text().splitlines():
        if line and not line.startswith('#'):
            n,a = map(int,line.split()); values[n]=a
    records=[]
    for n in (20,30):
        z,estimate = reconstruct(values[n])
        record={'n':n, 'backbone':mp.nstr(z,45), 'estimate':mp.nstr(estimate,45),
                'index_error':mp.nstr(estimate-n,45), 'certified':False}
        records.append(record)
        print(record)
    (out/'inverse_diagnostics.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':
    main()
