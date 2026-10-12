"""Full scalar density formula: ordinary series versus cut integral.

This independently checks the ordinary spectral difference, so the
Hurwitz-zeta derivative baseline cancels from both sides.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 55


def check(r, a, masses):
    a = mp.mpf(a)
    masses = list(map(mp.mpf, masses))
    N = len(masses)
    cutoff, order = 40, 26
    raw = [mp.mpf(0)] + [(-1)**(k+1)*sum(u**k for u in masses)/k
                          for k in range(1, order+1)]
    powers = [[mp.mpf(1)] + [mp.mpf(0)]*order]
    for q in range(1, r+1):
        powers.append([sum(powers[-1][j]*raw[k-j] for j in range(k+1))
                       for k in range(order+1)])

    def f(n):
        x = n+a
        B = 2*N*mp.log(x)
        L = sum(mp.log1p(mu/(x*x)) for mu in masses)
        return sum(mp.binomial(r,q)*B**(r-q)*L**q for q in range(1,r+1))

    direct = sum(f(n) for n in range(cutoff))
    for q in range(1,r+1):
        for k in range(q,order+1):
            log_tail = (-1)**(r-q)*mp.diff(
                lambda s: mp.zeta(s,cutoff+a), mp.mpf(2*k),r-q)
            direct += mp.binomial(r,q)*(2*N)**(r-q)*powers[q][k]*log_tail

    def Q(t):
        if not t:
            return mp.polygamma(1,a)
        b = mp.sqrt(t)
        return mp.im(mp.digamma(a+1j*b))/b

    maximum = max(masses)

    def density(t, count):
        if t > maximum:
            # Stable cancellation of common logarithmic behavior at infinity.
            delta = sum(mp.log1p(-mu/t) for mu in masses)
            base = N*(mp.log(t)+1j*mp.pi)
            return -mp.im(sum(mp.binomial(r,q)*base**(r-q)*delta**q
                              for q in range(1,r+1)))/mp.pi
        h = sum(mp.log(abs(mu-t)) for mu in masses)
        return -mp.im((h+1j*mp.pi*count)**r
                      -N**r*(mp.log(t)+1j*mp.pi)**r)/mp.pi

    integral = mp.mpf(0)
    endpoints = sorted(set([mp.mpf(0)]+masses))
    for left,right in zip(endpoints,endpoints[1:]):
        middle = (left+right)/2
        count = sum(mu < middle for mu in masses)
        integral += mp.quad(lambda t: density(t,count)*Q(t),
                            [left,middle,right])
    # Square-root substitution makes the large-mass tail inexpensive.
    lower = mp.sqrt(maximum)
    integral += mp.quad(lambda y: 2*y*density(y*y,N)*Q(y*y),
                        [lower,lower+1,2*lower+2,mp.inf])
    return dict(order=r,a=str(a),masses=list(map(str,masses)),
                direct_method=dict(cutoff=cutoff,power_terms=order,
                    description='Finite head plus convergent Hurwitz-zeta-derivative tail'),
                direct_difference=mp.nstr(direct,50),
                density_integral=mp.nstr(integral,50),
                absolute_residual=mp.nstr(abs(direct-integral),8))


if __name__ == '__main__':
    data = dict(working_digits=mp.mp.dps,
                status='Numerical diagnostics, not interval certificates',
                cases=[check(2,'0.7',['0.8','1.4']),
                       check(3,'0.7',['0.8','1.4'])])
    path=Path(__file__).resolve().parents[1] / 'data' / 'full_scalar_independent_checks.json'
    with open(path,'w',encoding='utf-8') as output:
        json.dump(data,output,indent=2)
        output.write('\n')
    print(json.dumps(data,indent=2))
