"""Independent high precision check using a single integral, not inversion.

Li_{a,b}(i,1) = i/(a-1)! int_0^1 (-log t)^{a-1}
                                   Li_b(it)/(1-it) dt.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp
import sympy as sp
import extend_weight8 as ex

mp.mp.dps=90

def beta(n):
    return (mp.zeta(n,mp.mpf(1)/4)-mp.zeta(n,mp.mpf(3)/4))/mp.power(4,n)

values={ex.G:beta(2),ex.B4:beta(4),ex.B6:beta(6),ex.B8:beta(8),
        ex.Z3:mp.zeta(3),ex.Z5:mp.zeta(5),ex.Z7:mp.zeta(7),ex.lg:mp.log(2)}

def evaluate(expr):
    f=sp.lambdify(list(values),expr,'mpmath')
    return f(*values.values())

def integral(a,b):
    f=lambda t:1j*(-mp.log(t))**(a-1)*mp.polylog(b,1j*t)/(1-1j*t)
    return mp.im(mp.quad(f,[0,mp.mpf('0.01'),mp.mpf('0.2'),1])/mp.factorial(a-1))

def run(output):
    result=[]
    for w in (6,8):
        for b in range(1,w):
            a=w-b
            expected=evaluate(ex.g(a,b))
            observed=integral(a,b)
            error=abs(expected-observed)
            print((a,b),'g =',mp.nstr(observed,25),'abs error =',mp.nstr(error,8),flush=True)
            assert error<mp.mpf('1e-83')
            result.append({'a':a,'b':b,'value':mp.nstr(observed,85),
                           'absolute_residual':mp.nstr(error,12)})
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open('w') as out:
        json.dump({'mpmath_dps':mp.mp.dps,'method':'single integral along radius to i',
                   'status':'Numerical quadrature cross-checks, not interval certificates.',
                   'checks':result},out,indent=2)
        out.write('\n')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=
        Path(__file__).resolve().parents[3]/'results'/'independent'/'parity'/'quadrature_checks.json')
    args=parser.parse_args()
    run(args.output)
