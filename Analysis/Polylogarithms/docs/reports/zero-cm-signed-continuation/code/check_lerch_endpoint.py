"""Numerical-only checks of the logarithmic rho->1 endpoint law.

The difference of kernels is evaluated directly to avoid subtracting two
nearly equal special-function values. These are diagnostics, not intervals.
Requires mpmath. Writes results/lerch_endpoint_diagnostics.json in the package.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps=65


def appell(n,v):
    coeff=mp.taylor(lambda z:1/mp.gamma(1+z),0,n)
    return sum(mp.factorial(n)/mp.factorial(n-j)*coeff[j]*v**(n-j)
               for j in range(n+1))


def difference(n,a,epsilon):
    rho=mp.exp(-epsilon)
    delta=-mp.expm1(-epsilon)
    coeff=mp.taylor(lambda z:1/mp.gamma(1+z),0,n)

    def integrand(v):
        x=mp.exp(v)
        u=-mp.expm1(-x)
        Q=sum(mp.factorial(n)/mp.factorial(n-j)*coeff[j]*v**(n-j)
              for j in range(n+1))
        return (-1)**n*delta*mp.exp(2*v-(a+1)*x)*Q/(u*(delta+rho*u))

    ell=mp.log(epsilon)
    grid=sorted(set([mp.mpf(-150),ell-5,ell,ell+5,mp.mpf(-5),mp.mpf(0),mp.log(200/a)]))
    return mp.quad(integrand,grid)


if __name__=='__main__':
    records=[]
    for n in (0,3,4):
        for power in (4,8,12):
            epsilon=mp.mpf(10)**(-power)
            a=mp.mpf(1)
            actual=difference(n,a,epsilon)
            L=mp.log(1/epsilon)
            leading=epsilon*L**(n+1)/(n+1)
            row=dict(n=n,k=1,a='1',epsilon=mp.nstr(epsilon,8),
                     difference=mp.nstr(actual,32),leading=mp.nstr(leading,32),
                     ratio=mp.nstr(actual/leading,20),
                     next_scale_residual=mp.nstr((actual-leading)/(epsilon*L**n),20))
            records.append(row)
            print(row,flush=True)
    result=dict(status='ordinary high-precision diagnostics; not certified enclosures',
                precision_digits=mp.mp.dps,records=records)
    (Path(__file__).resolve().parents[1] / "results" / "lerch_endpoint_diagnostics.json").write_text(json.dumps(result,indent=2)+'\n')
