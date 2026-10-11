"""Numerical and finite symbolic diagnostics for mixed Dougall identities.

Proofs are in sections/03_dougall.tex. Numerical quadrature / Euler--
Maclaurin here is a diagnostic, not a proof or interval certificate.
"""
from __future__ import annotations
import json
import argparse
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 65
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results/dougall.json")
args = parser.parse_args()
OUT = args.output
OUT.parent.mkdir(parents=True, exist_ok=True)
rows = []


def record(name, lhs, rhs, extra=None):
    row = {"name": name, "lhs": mp.nstr(lhs, 42), "rhs": mp.nstr(rhs, 42),
           "absolute_error": mp.nstr(abs(lhs-rhs), 8)}
    if extra:
        row.update(extra)
    rows.append(row)
    assert abs(lhs-rhs) < mp.mpf("1e-40"), row
    print(name, row["absolute_error"], flush=True)


def summation(f, n0=250):
    tail, estimate = mp.sumem(f, [n0, mp.inf], error=True)
    return mp.fsum(f(n) for n in range(n0)) + tail, estimate


def Q(n, a, p, q):
    return mp.exp(mp.loggamma(n+a)+mp.loggamma(n+1+p)+mp.loggamma(n+1+q)
                  +mp.loggamma(n+a-p-q)-mp.loggamma(n+1)
                  -mp.loggamma(n+a-p)-mp.loggamma(n+a-q)
                  -mp.loggamma(n+1+p+q))


def centered(a, p=0, q=0, t=0, order=11, mixed=False):
    """Centered coefficients and, optionally, their p,q mixed derivative.

    This finite polynomial computation uses Bernoulli polynomials only.
    It avoids numerical differentiation of large, cancelling log-Gammas.
    At mixed=True p=q=0 is required; symmetry gives C_p=C_q.
    """
    eta=a/2
    shifts=[eta,1+p-eta,1+q-eta,eta-p-q-t]
    h=[mp.mpf(0)]
    hp=[mp.mpf(0)]
    hpq=[mp.mpf(0)]
    for j in range(1,order+1):
        h.append(-sum(mp.bernpoly(2*j+1,v) for v in shifts)/(j*(2*j+1)))
        if mixed:
            hp.append(-(mp.bernpoly(2*j,1-eta)-mp.bernpoly(2*j,eta-t))/j)
            hpq.append(-2*mp.bernpoly(2*j-1,eta-t))
    C=[mp.mpf(1)]; Cp=[mp.mpf(0)]; Cpq=[mp.mpf(0)]
    for j in range(1,order+1):
        C.append(sum(k*h[k]*C[j-k] for k in range(1,j+1))/j)
        if mixed:
            Cp.append(sum(k*(hp[k]*C[j-k]+h[k]*Cp[j-k])
                          for k in range(1,j+1))/j)
            Cpq.append(sum(k*(hpq[k]*C[j-k]+2*hp[k]*Cp[j-k]+h[k]*Cpq[j-k])
                           for k in range(1,j+1))/j)
    return Cpq if mixed else C


def subtractive_sum(f,a,coefficients,t=0,n0=180,derivative_coefficients=None):
    """Direct sum plus explicit centered asymptotic tail.

    The last retained asymptotic term is recorded as a numerical
    convergence diagnostic, not a rigorous tail-error bound.
    """
    pieces=[]
    for j in range(2,len(coefficients)):
        s=2*j-1+2*t
        if derivative_coefficients is None:
            pieces.append(coefficients[j]*mp.zeta(s,n0+a/2))
        else:
            pieces.append(derivative_coefficients[j]*mp.zeta(s,n0+a/2)
                          +2*coefficients[j]*mp.diff(lambda z:mp.zeta(z,n0+a/2),s))
    return mp.fsum(f(n) for n in range(n0))+mp.fsum(pieces),abs(pieces[-1])


for a in [mp.mpf('0.5'), mp.mpf('1'), mp.mpf('1.5'), mp.mpf('2.3')]:
    f = lambda n: (n+a/2)*(mp.polygamma(1,n+a)-mp.polygamma(1,n+1))**2
    lhs, estimate = summation(f)
    rhs = ((a-1)*mp.polygamma(2,a)/4 + (mp.polygamma(1,a)-mp.zeta(2))/2
           +mp.mpf('1.5')*(a-1)*mp.zeta(3))
    record("trigamma_square_a="+str(a), lhs, rhs,
           {"tail_error_estimate": mp.nstr(estimate,8)})


for a,p,q in [(mp.mpf('1.7'),mp.mpf('.08'),mp.mpf('-.06')),
              (mp.mpf('.6'),mp.mpf('.025'),mp.mpf('.04'))]:
    A=a-1
    f=lambda n: (n+a/2)*(Q(n,a,p,q)-1)+(A-p-q)*p*q/(n+a/2)
    lhs,estimate=subtractive_sum(f,a,centered(a,p,q))
    B=mp.digamma(a/2)+(mp.digamma(2)-mp.digamma(1+p)
                      -mp.digamma(1+q)-mp.digamma(a-p-q))/2
    rhs=-(A-p-q)*p*q*B
    record("two_parameter_generator_a="+str(a),lhs,rhs,
           {"p":str(p),"q":str(q),"last_asymptotic_tail_term":mp.nstr(estimate,8)})


def mixed_spectral_data(a,t):
    A=a-1
    F=mp.gamma(a-t)/(mp.gamma(a)*mp.gamma(1+t)*(1-t))
    V=mp.digamma(1)-mp.digamma(a-t)+mp.digamma(a)-mp.digamma(1+t)
    W=mp.polygamma(1,a-t)-mp.polygamma(1,a)
    D=F*(2*t*(1+t*V)-A*((1+t*V)**2+t*t*W))
    return D/(2*t)+(A-2*t)*mp.zeta(1+2*t,a/2)


for a,t in [(mp.mpf('1.5'),mp.mpf('.09')),
            (mp.mpf('.7'),mp.mpf('-.06')),
            (mp.mpf('1'),mp.mpf('.05'))]:
    A=a-1
    def f(n):
        x=n+a/2
        R=x*mp.gamma(n+1)*mp.gamma(n+a-t)/(mp.gamma(n+a)*mp.gamma(n+1+t))
        L=mp.digamma(n+1)-mp.digamma(n+a-t)+mp.digamma(n+a)-mp.digamma(n+1+t)
        K=mp.polygamma(1,n+a-t)-mp.polygamma(1,n+1+t)
        return R*(L*L+K)+(A-2*t)*x**(-1-2*t)
    lhs,estimate=subtractive_sum(f,a,centered(a,t=t,mixed=True),t=t)
    record("mixed_spectral_generator_a="+str(a),lhs,mixed_spectral_data(a,t),
           {"t":str(t),"last_asymptotic_tail_term":mp.nstr(estimate,8)})


for a in [mp.mpf('0.5'),mp.mpf('1'),mp.mpf('1.5'),mp.mpf('2')]:
    A=a-1
    def f(n):
        x=n+a/2
        l2=mp.polygamma(1,n+a)-mp.polygamma(1,n+1)
        l3=-mp.polygamma(2,n+a)-mp.polygamma(2,n+1)
        mu=-mp.digamma(n+a)-mp.digamma(n+1)
        return x*(l3+mu*l2)-(2+2*A*mp.log(x))/x
    C=centered(a,mixed=True)
    Ct=[mp.diff(lambda t:centered(a,t=t,mixed=True)[j],0) for j in range(len(C))]
    lhs,estimate=subtractive_sum(f,a,C,derivative_coefficients=Ct)
    ell=1+mp.euler-mp.digamma(a)
    d=mp.polygamma(1,a)-mp.zeta(2)
    rhs=2*mp.digamma(a/2)+ell-A*(ell*ell+5*d+1)/4-2*A*mp.stieltjes(1,a/2)
    record("first_mixed_spectral_jet_a="+str(a),lhs,rhs,
           {"last_asymptotic_tail_term":mp.nstr(estimate,8)})


# Independent finite polynomial calculations: mixed Bell entries and the
# residue-locus factorization. All arithmetic in this block is exact.
p,q=sp.symbols('p q')
lam=sp.symbols('L0:7')
L=sp.Add(*[lam[r+s]*p**r*q**s/(sp.factorial(r)*sp.factorial(s))
           for r in range(1,6) for s in range(1,6) if r+s<=6])
Qtr=sp.expand(sum(L**k/sp.factorial(k) for k in range(4)))
expected={(1,1):lam[2],(2,1):lam[3],(3,1):lam[4],
          (2,2):lam[4]+2*lam[2]**2,
          (3,2):lam[5]+6*lam[2]*lam[3],
          (3,3):lam[6]+9*lam[2]*lam[4]+9*lam[3]**2+6*lam[2]**3}
symbolic=[]
for (r,s),value in expected.items():
    got=Qtr.coeff(p,r).coeff(q,s)*sp.factorial(r)*sp.factorial(s)
    residual=sp.expand(got-value)
    assert residual==0
    symbolic.append({"r":r,"s":s,"mixed_derivative":str(value),"residual":"0"})

x,eta,b=sp.symbols('x eta b')
grid=[]
for N in range(1,7):
    for k in range(1,N+1):
        n=x-eta; a=2*eta
        gamma_cancelled=x*sp.rf(n+1,k-1)*sp.rf(n+1+a-k,k-1)
        gamma_cancelled*=sp.rf(n+1+a-b,N-k)*sp.rf(n+b+k-N,N-k)
        predicted=x*sp.prod(x*x-(eta-r)**2 for r in range(1,k))
        predicted*=sp.prod(x*x-(eta+1-b+r)**2 for r in range(N-k))
        assert sp.expand(gamma_cancelled-predicted)==0
        grid.append({"N":N,"integer_c":k,"residual":"0"})

OUT.write_text(json.dumps({"decimal_precision":mp.mp.dps,
                          "status":"diagnostics only; proofs in accompanying TeX",
                          "all_thresholds_passed": True,
                          "numerical":rows,"exact_bell":symbolic,
                          "exact_grid_polynomials":grid},indent=2)+"\n")
print(OUT,flush=True)
