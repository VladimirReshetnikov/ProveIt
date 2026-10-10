#!/usr/bin/env python3
"""Non-interval diagnostics; use the Laplace integral to avoid a long Lerch tail."""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps=45


def integrals(a,u):
    eta=mp.exp(-u)
    cuts=[0,eta,mp.sqrt(eta),mp.mpf('.1'),1,10,mp.inf]
    def density(x,r=0,j=0):
        if not x:
            return mp.mpf(0)
        q=(mp.log(x)+mp.euler)**2-mp.zeta(2)
        return ((-1)**j*mp.factorial(r)*x**(2+j)*mp.exp(-(a+r)*x)*q
                /(-mp.expm1(-x-eta))**(r+1))
    return tuple(mp.quad(lambda x:density(x,r,j),cuts)
                 for r,j in [(0,0),(1,0),(0,1),(2,0)])


def main():
    a,u=mp.findroot(lambda a,u:integrals(a,u)[:2],
                  (mp.mpf('1.2998'),mp.mpf('9.2')),tol=mp.mpf('1e-32'))
    F,Fr,Fa,Frr=integrals(a,u)
    result={'status':'non-interval Laplace-integral diagnostic; analytic theorem proves existence and uniqueness',
            'precision':mp.mp.dps,'a_min':mp.nstr(a,38),'rho_min':mp.nstr(mp.exp(-mp.exp(-u)),38),
            'eta_min':mp.nstr(mp.exp(-u),38),'F':mp.nstr(F,8),'F_rho':mp.nstr(Fr,8),
            'F_a':mp.nstr(Fa,32),'F_rho_rho':mp.nstr(Frr,32),
            'a_second_derivative':mp.nstr(-Frr/Fa,32)}
    result_dir=Path(__file__).resolve().parents[2]/'results'/'lerch'
    result_dir.mkdir(parents=True,exist_ok=True)
    (result_dir/'minimum_diagnostic.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)


if __name__=='__main__':
    main()
