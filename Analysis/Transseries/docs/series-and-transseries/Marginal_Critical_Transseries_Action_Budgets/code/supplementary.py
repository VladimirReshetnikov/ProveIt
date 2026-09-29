#!/usr/bin/env python3
"""Additional exact and numerical checks; no interval-arithmetic claim."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
import sympy as sp
from verify import Model, fmt

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    mp.mp.dps = 40
    r, x = sp.symbols('r x')
    K = sum(x**k/(sp.factorial(k)*(k-1)) for k in range(2,9))
    S = r
    for _ in range(8):
        S = sp.series(r-r*K.subs(x,S),r,0,8).removeO().expand()
    residual = sp.series(S+r*K.subs(x,S)-r,r,0,8).removeO().expand()
    for j in range(8):
        assert residual.coeff(r,j) == 0
    b, ell, H, lam, gam, Jphi = sp.symbols('b ell H lam gamma Jphi',positive=True)
    nu = b+gam-sp.Rational(3,2)
    uncancelled = (lam**2-1)*(nu+sp.log(ell)-sp.log(H)/2+ell**-2)/2 \
                 - Jphi-b*(lam**2-1)/2
    universal = (lam**2-1)*(gam-sp.Rational(3,2)+sp.log(ell)-sp.log(H)/2+ell**-2)/2-Jphi
    assert sp.simplify(uncancelled-universal) == 0
    out = {'exact_checks_passed':9,'fold_S_series':str(S),
           'precision_decimal':40,'interval_arithmetic':False,'window':[],'fold':[]}
    phi = lambda y: mp.exp(-y*y/2)/mp.sqrt(2*mp.pi)
    for d in ['0','0.5']:
        model = Model(d)
        n=10**8
        Hn,B,N=model.scale(n)
        M=int(N); en=mp.mpf(M)/N
        for la in ['-1','1']:
            y=mp.mpf(la)
            print(f'Window delta={d}, lambda={la}',flush=True)
            J=mp.quad(lambda t:(mp.exp(mp.j*y*t-t*t/2)*t*t/2*mp.log(-mp.j*t)).real,
                      [0,.25,1,3,6,10,16,mp.inf])/mp.pi
            beta=model.beta*(1+y*B/n)
            ratio=mp.exp(-n*beta*mp.zeta(3,M+1))*model.probability(n,M,la)/model.probability(n,None,la)
            leading=mp.exp(-1/(2*en**2))
            correction=1+y/(en*mp.sqrt(Hn))+(y*y-1)/(2*Hn)*(mp.euler-mp.mpf('1.5')+mp.log(en)-mp.log(Hn)/2+en**-2)-J/(Hn*phi(y))
            out['window'].append({'delta1':d,'n':n,'lambda':la,'M':M,
                'actual_ratio':fmt(ratio),'leading':fmt(leading),'corrected':fmt(leading*correction)})
        for M in [100,1000,10000]:
            print(f'Fold delta={d}, M={M}',flush=True)
            L=mp.log(M)+model.nu
            # Entire K(s), evaluated as a rapidly convergent small-s series.
            kfun=lambda s:mp.fsum(s**k/(mp.factorial(k)*(k-1)) for k in range(2,36))
            Snum=mp.findroot(lambda s:L*s+kfun(s)-1,1/L)
            v=mp.findroot(lambda v:model.beta*(mp.fsum(mp.exp(j*v)/mp.mpf(j)**2 for j in range(1,M+1))+model.delta*mp.exp(v))-1,
                          (Snum/M,mp.mpf('1.01')*Snum/M))
            drift=v-model.beta*(mp.fsum(mp.exp(j*v)/mp.mpf(j)**3 for j in range(1,M+1))+model.delta*mp.exp(v)-model.F1)
            curvature=model.beta*(mp.fsum(mp.exp(j*v)/mp.mpf(j) for j in range(1,M+1))+model.delta*mp.exp(v))
            Q=mp.fsum(Snum**k/(mp.factorial(k)*(k-2)) for k in range(3,36))
            pred=model.A/M**2*(mp.mpf('.5')+Snum-L*Snum*Snum/2-Q)
            out['fold'].append({'delta1':d,'M':M,'M_L_v':fmt(M*L*v),
               'scaled_drift':fmt(2*M*M*drift/model.A),
               'drift_prediction':fmt(2*M*M*pred/model.A),
               'curvature_over_A_L':fmt(curvature/(model.A*L)),
               'M2L_root_error':fmt(M*M*L*(v-Snum/M))})
    # ProveIt edit (2026-09-29): LF line endings on every platform.
    (ROOT/'data'/'supplementary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'status':'all supplementary assertions passed','exact_checks':9}))

if __name__=='__main__':
    main()
