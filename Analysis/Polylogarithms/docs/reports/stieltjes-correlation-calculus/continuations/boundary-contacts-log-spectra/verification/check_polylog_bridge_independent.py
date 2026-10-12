"""Independent checks of the logarithmic-density/polylogarithm bridge.

Interior polylogarithms on the right are evaluated by their convergent
strict harmonic series, without using the integral transformation.
These computations are numerical diagnostics, not interval certificates.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 65


def polynomial(r, y):
    return sum((-1)**h*mp.binomial(r, 2*h+1)*mp.pi**(2*h)
               *y**(r-2*h-1) for h in range((r-1)//2+1))


def integral(r, order, z):
    def integrand(t):
        y = mp.log1p(-t)-mp.log(t)
        polylog = -mp.log1p(-z*t) if order == 1 else mp.polylog(order, z*t)
        return polynomial(r, y)*polylog/t
    return mp.quad(integrand,
                   [0,mp.mpf('0.1'),mp.mpf('0.5'),mp.mpf('0.9'),1])


def strict_series(r, order, z, terms=260):
    # e[d] = H_{n-1}(1,...,1), d=r-1. Update descending to preserve
    # strict distinct indices when adjoining the next reciprocal 1/n.
    depth = r-1
    elementary = [mp.mpf(1)]+[mp.mpf(0)]*depth
    summands = []
    for n in range(1,terms+1):
        summands.append(z**n*elementary[depth]/n**(order+1))
        for d in range(depth,0,-1):
            elementary[d] += elementary[d-1]/n
    return (-1)**(r-1)*mp.factorial(r)*mp.fsum(summands)


if __name__ == '__main__':
    interior=[]
    for r,order,ztext in [(2,2,'0.4'),(3,1,'0.3')]:
        z=mp.mpf(ztext)
        lhs=integral(r,order,z)
        rhs=strict_series(r,order,z)
        interior.append(dict(r=r,polylog_order=order,z=ztext,
            series_terms=260,
            lhs_integral=mp.nstr(lhs,58),rhs_strict_harmonic_series=mp.nstr(rhs,58),
            absolute_residual=mp.nstr(abs(lhs-rhs),8)))
    endpoint_lhs=integral(3,1,mp.mpf(1))
    endpoint_rhs=mp.pi**4/15
    half_lattice=[]
    for ttext in ['0.1','1','4']:
        t=mp.mpf(ttext)
        b=mp.sqrt(t)
        q=mp.im(mp.digamma(mp.mpf('0.5')+1j*b))/b
        elementary=mp.pi*mp.tanh(mp.pi*b)/(2*b)
        half_lattice.append(dict(t=ttext,
            digamma_value=mp.nstr(q,58),elementary_value=mp.nstr(elementary,58),
            absolute_residual=mp.nstr(abs(q-elementary),8)))
    # Test the nonintegral Mellin generating function independently.
    s,w=mp.mpf('1.3'),mp.mpf('0.2')
    generating_lhs=(mp.sin(mp.pi*w)/mp.pi
        *mp.quad(lambda t: t**(s-w-1)*(1-t)**w,[0,mp.mpf('0.5'),1]))
    generating_rhs=w*mp.gamma(s-w)/(mp.gamma(s+1)*mp.gamma(1-w))
    data=dict(working_digits=mp.mp.dps,
        status='Numerical diagnostics, not interval certificates',
        interior=interior,
        endpoint=dict(r=3,polylog_order=1,z='1',
            lhs_integral=mp.nstr(endpoint_lhs,58),rhs_pi4_over15=mp.nstr(endpoint_rhs,58),
            absolute_residual=mp.nstr(abs(endpoint_lhs-endpoint_rhs),8)),
        half_lattice=half_lattice,
        mellin_generator=dict(s=str(s),w=str(w),
            lhs_beta_integral=mp.nstr(generating_lhs,58),
            rhs_gamma_quotient=mp.nstr(generating_rhs,58),
            absolute_residual=mp.nstr(abs(generating_lhs-generating_rhs),8)))
    path=Path(__file__).resolve().parents[1] / 'data' / 'polylog_bridge_independent_checks.json'
    with open(path,'w',encoding='utf-8') as output:
        json.dump(data,output,indent=2)
        output.write('\n')
    print(json.dumps(data,indent=2))
