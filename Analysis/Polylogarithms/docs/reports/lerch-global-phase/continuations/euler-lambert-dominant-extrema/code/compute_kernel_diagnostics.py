#!/usr/bin/env python3
"""High-precision stationary-kernel diagnostics; not a global certificate.

The N=2 global optimum has a separate exact certificate. At other finite
indices these are stationary candidates; analytic global results are in
the article. Default output: data/kernel_diagnostics.json.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "data/kernel_diagnostics.json")
    args = parser.parse_args()
    mp.mp.dps = 85
    yinf = mp.findroot(lambda y: 1+y-y*y-y**3+4*y*mp.log(y), (mp.mpf('.1'), mp.mpf('.2')))
    cinf = -2*mp.log(yinf)/(1-yinf*yinf)
    minf = (1+yinf)*yinf**(2*yinf*yinf/(1-yinf*yinf))
    kappa = cinf**2*yinf*yinf*(1+yinf)*mp.exp(-cinf*yinf*yinf)/2
    H = lambda c, y: (mp.exp(-c*y*y)-mp.exp(-c))/(1-y)
    H1 = lambda c, y: (mp.exp(-c)*(c+c*c/2)
                      -mp.exp(-c*y*y)*(c*y*y+(c*y*y)**2/2))/(1-y)
    hessian = mp.matrix([[mp.diff(H,(cinf,yinf),(2,0)),mp.diff(H,(cinf,yinf),(1,1))],
                         [mp.diff(H,(cinf,yinf),(1,1)),mp.diff(H,(cinf,yinf),(0,2))]])
    drift = -mp.lu_solve(hessian,mp.matrix([mp.diff(H1,(cinf,yinf),(1,0)),
                                           mp.diff(H1,(cinf,yinf),(0,1))]))
    rows=[]
    guess=(mp.mpf('1.5'),mp.mpf('.25'))
    for n in [2,3,4,5,10,20,50,100,200,1000,10000]:
        def kernel(c,y):
            r=c/n
            return (((1-r*y*y)**n/(1+r*y*y)) - ((1-r)**n/(1+r)))/(1-y)
        dc=lambda c,y:mp.diff(kernel,(c,y),(1,0))
        dy=lambda c,y:mp.diff(kernel,(c,y),(0,1))
        c,y=mp.findroot((dc,dy),guess,tol=mp.mpf('1e-75'),maxsteps=80)
        assert 0<c<n and 0<y<1
        hcc=mp.diff(kernel,(c,y),(2,0))
        hcy=mp.diff(kernel,(c,y),(1,1))
        hyy=mp.diff(kernel,(c,y),(0,2))
        assert hcc<0 and hcc*hyy-hcy*hcy>0
        value=kernel(c,y)
        rows.append({"N":n,"scaled_coordinate":mp.nstr(c,50),
                     "r":mp.nstr(c/n,50),"y":mp.nstr(y,50),
                     "stationary_value":mp.nstr(value,50),
                     "N_times_excess_over_limit":mp.nstr(n*(value-minf),50),
                     "maximum_gradient_residual":mp.nstr(max(abs(dc(c,y)),abs(dy(c,y))),8)})
        guess=(c,y)
    report={"status":"numerical stationary-point diagnostic, not an interval certificate",
            "decimal_precision":mp.mp.dps,"mpmath_version":mp.__version__,
            "limit":{"y":mp.nstr(yinf,60),"c":mp.nstr(cinf,60),
                     "M":mp.nstr(minf,60),"kappa":mp.nstr(kappa,60),
                     "first_location_correction_c":mp.nstr(drift[0],50),
                     "first_location_correction_y":mp.nstr(drift[1],50)},
            "rows":rows}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(f"Computed {len(rows)} stationary candidates; wrote {args.output}")

if __name__=='__main__':
    main()
