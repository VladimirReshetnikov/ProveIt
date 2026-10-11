#!/usr/bin/env python3
"""Independent diagnostics for the next two-particle Gauss resonance.

No PSLQ, no fitted constants. Finite sums use their defining weight
recurrence. Asymptotic residuals are diagnostics, not certified error bounds.
"""
import json
from pathlib import Path
import sys
import mpmath as mp
import sympy as sp

mp.mp.dps = 80
OUT = Path(__file__).with_name("second_resonance_checks.json")


def parameters(a, c):
    mu = 1/(a*c)
    h = 1/a+1/c
    q = 1+h
    rho = mp.digamma(1)-mp.digamma(a+1)-mp.digamma(c+1)
    tau = mp.polygamma(1, 1)-mp.polygamma(1, a+1)-mp.polygamma(1, c+1)
    r2 = rho*rho+tau
    lam = -q-2*rho
    constant = -rho*rho-q*rho-2
    C1 = -rho*r2-q*rho*rho-q*r2/2-(2*mu+q+1)*rho-q-mu/2
    return mu, h, q, rho, tau, r2, lam, constant, C1


def germ(u, a, c, alpha):
    mu = 1/(a*c)
    R = (mp.gamma(a+1)*mp.gamma(c+1)*mp.gamma(1+u)
         / (mp.gamma(a+1+u)*mp.gamma(c+1+u)))
    beta = -(a*c+a+c)-(a+c+mp.mpf(".5"))*u-u*u/2
    P = (a+u)*(c+u)*mu*R*R
    T = mu*R*(beta+alpha*u)
    V = 1/(1-u*u)
    return (P/(u*u*(u-1))-mu*R*mp.zeta(u,alpha)
            -T*mp.zeta(1+u,alpha)+2*R/u*mp.zeta(1+u,alpha)
            -2*V/u*mp.zeta(1+2*u,alpha))


def counterterm(u, a, c, alpha, n):
    y = n+alpha
    mu = 1/(a*c)
    R = (mp.gamma(a+1)*mp.gamma(c+1)*mp.gamma(1+u)
         / (mp.gamma(a+1+u)*mp.gamma(c+1+u)))
    beta = -(a*c+a+c)-(a+c+mp.mpf(".5"))*u-u*u/2
    return (mu*R*y**(-u)+mu*R*(beta+alpha*u)*y**(-1-u)
            +2/u*(y**(-1-2*u)/(1-u*u)-R*y**(-1-u)))


def explicit_jets(a, c, alpha):
    mu, h, q, rho, tau, r2, lam, C, C1 = parameters(a,c)
    B = r2+q*rho+q-3+mu*(mp.mpf(".5")-alpha)
    g0, g1, g2 = [mp.stieltjes(k, alpha) for k in range(3)]
    D0 = C-mu-lam*g0+2*g1
    D1 = (C1-mu*mp.diff(lambda v:mp.zeta(v,alpha),0)
          +B*g0+lam*g1-3*g2)
    return D0, D1, B


def finite_moments(a, c, u, sizes):
    b = a+c+1+u
    w = mp.gamma(a)*mp.gamma(c)/mp.gamma(b)
    psi = mp.digamma(b)
    M = [mp.mpf(0) for _ in range(3)]
    D = [mp.mpf(0) for _ in range(3)]
    out = []
    for n in range(max(sizes)+1):
        for j in range(3):
            p = n**j
            M[j] += p*w
            D[j] -= p*w*psi
        if n in sizes:
            S = M[0]*M[2]-M[1]*M[1]
            S1 = D[0]*M[2]+M[0]*D[2]-2*M[1]*D[1]
            out.append((n, list(M), S, S1))
        w *= (n+a)*(n+c)/((n+b)*(n+1))
        psi += 1/(n+b)
    return out


def s(x):
    return mp.nstr(x, 35)


report = {"precision_digits":mp.mp.dps,
          "software":{"python":sys.version.split()[0],"mpmath":mp.__version__,"sympy":sp.__version__},
          "symbolic":{}, "germ_jets":[],
          "finite_cutoffs":[], "convergent_partition_checks":[],
          "accelerated_defining_series":[], "polylogarithmic_checks":[]}
n,a,c,u = sp.symbols("n a c u")
sac = a*c+a+c
ratio = (n+a)*(n+c)/((n+a+c+1+u)*(n+1))
t = n*(n+a+c+u)
t_next = (n+1)*(n+1+a+c+u)*ratio
report["symbolic"]["pearson_zero_moment"] = sp.simplify(t_next-t-(a*c-u*n)) == 0
report["symbolic"]["pearson_first_moment"] = sp.simplify((n+1)*t_next-n*t-((1-u)*n*n+sac*n+a*c)) == 0

mu,h,rho,r2,r3,alpha = sp.symbols("mu h rho r2 r3 alpha")
q = 1+h
R = 1+rho*u+r2*u*u/2+r3*u**3/6
P = (1+h*u+mu*u*u)*R*R
T = R*(-q+(mu*(alpha-sp.Rational(1,2))-h)*u-mu*u*u/2)
V = 1+u*u
numer = sp.series(P/(u-1)+2*R-V-u*T,u,0,4).removeO().expand()
C = -rho*rho-q*rho-2
G0 = C-mu*(alpha+sp.Rational(1,2))
G1 = (-rho*r2-q*rho*rho-q*r2/2
      -(mu*(alpha+sp.Rational(3,2))+q+1)*rho-q-mu/2)
report["symbolic"]["two_pole_cancellation"] = all(sp.simplify(numer.coeff(u,j))==0 for j in [0,1])
report["symbolic"]["G0_reduction"] = sp.simplify(numer.coeff(u,2)-G0)==0
report["symbolic"]["G1_reduction"] = sp.simplify(numer.coeff(u,3)-G1)==0
euler_gamma,zeta2 = sp.symbols("euler_gamma zeta2")
raw_F = zeta2-2+2*euler_gamma-2*euler_gamma**2
normalized_F = raw_F-2*euler_gamma*(1-2*euler_gamma)-euler_gamma**2-(euler_gamma**2+zeta2)
report["symbolic"]["normalization_gamma_finite_part"] = sp.simplify(normalized_F+2)==0
report["symbolic"]["normalization_rational_finite_part"] = sp.series(1/(u*u*(u-1)*(1+u)**2),u,0,1).removeO().expand().coeff(u,0)==-2

epsilon = mp.mpf("1e-18")
for av,cv,al in [(mp.mpf(".7"),mp.mpf("1.3"),mp.mpf(".6")),
                 (mp.mpf("1.25"),mp.mpf(".4"),mp.mpf("1.7")),
                 (mp.mpf(1),mp.mpf(1),mp.mpf(1))]:
    D0,D1,B = explicit_jets(av,cv,al)
    gp,gm = germ(epsilon,av,cv,al),germ(-epsilon,av,cv,al)
    mu,hh,qq,rho,tau,r2,lam,C,C1 = parameters(av,cv)
    nn = 11
    yy = nn+al
    Q0 = mu+(lam-2*mp.log(yy))/yy
    Q1 = mu*(rho-mp.log(yy))+(3*mp.log(yy)**2-lam*mp.log(yy)-B)/yy
    qp,qm = counterterm(epsilon,av,cv,al,nn),counterterm(-epsilon,av,cv,al,nn)
    report["germ_jets"].append({"a":s(av),"c":s(cv),"alpha":s(al),
      "D0":s(D0),"D1":s(D1),
      "D0_symmetric_error":s(abs((gp+gm)/2-D0)),
      "D1_symmetric_error":s(abs((gp-gm)/(2*epsilon)-D1)),
      "Q0_symmetric_error":s(abs((qp+qm)/2-Q0)),
      "Q1_symmetric_error":s(abs((qp-qm)/(2*epsilon)-Q1))})

mp.mp.dps = 45
for av,cv in [(mp.mpf(1),mp.mpf(1)), (mp.mpf(".7"),mp.mpf("1.3")),
              (mp.mpf("1.25"),mp.mpf(".4"))]:
    mu,hh,qq,rho,tau,r2,lam,C,C1 = parameters(av,cv)
    nu = r2+qq*rho+qq-3+mu
    for N,M,S,S1 in finite_moments(av,cv,mp.mpf(0),{100,1000,10000}):
        ln = mp.log(N)
        approx = mu*N-ln*ln+lam*ln+C
        approx1 = (-mu*N*ln+mu*(rho+1)*N+ln**3-lam*ln**2/2
                   -nu*ln+C1+mu*rho)
        exact_identity = av*cv*N*M[0]*M[0]-(av*cv+av+cv)*M[0]*M[1]-M[1]*M[1]
        report["finite_cutoffs"].append({"a":s(av),"c":s(cv),"N":N,
          "constant":s(C),"exact_pearson_determinant_error":s(abs(S-exact_identity)),
          "cutoff_asymptotic_error":s(S-approx),
          "first_derivative_asymptotic_error":s(S1-approx1)})

for av,cv,uv in [(mp.mpf(".7"),mp.mpf("1.3"),mp.mpf("4.2")),
                 (mp.mpf("1.25"),mp.mpf(".4"),mp.mpf("4.7"))]:
    N,M,S,S1 = finite_moments(av,cv,uv,{4000})[0]
    R = mp.gamma(av+1)*mp.gamma(cv+1)*mp.gamma(1+uv)/(mp.gamma(av+1+uv)*mp.gamma(cv+1+uv))
    product = (av+uv)*(cv+uv)*R*R/(av*cv*uv*uv*(uv-1))
    report["convergent_partition_checks"].append({"a":s(av),"c":s(cv),"u":s(uv),
       "N":N,"partition_product":s(product),"finite_partition":s(S),
       "absolute_truncation_error":s(abs(S-product))})


def gamma_ratio_coeffs(av, bv, count):
    """Bernoulli expansion of Gamma(n+a)/Gamma(n+b), divided by n**(a-b)."""
    logc = [mp.mpf(0)]
    for j in range(1,count+1):
        logc.append((-1)**(j+1)*(mp.bernpoly(j+1,av)-mp.bernpoly(j+1,bv))/(j*(j+1)))
    coeff = [mp.mpf(1)]
    for j in range(1,count+1):
        coeff.append(sum(k*logc[k]*coeff[j-k] for k in range(1,j+1))/j)
    return coeff


def accelerated_c1_series(av, uv, al, cutoff, count):
    """Uses finite defining moments plus independently expanded gamma tails.

    For c=1 the exact K_n is A*w_n times a quadratic plus w_n**2
    times a cubic. This follows directly from finite telescoping.
    No infinite partition product is used in this approximation.
    """
    cc = gamma_ratio_coeffs(av,av+2+uv,count)
    dd = [sum(cc[j]*cc[k-j] for j in range(k+1)) for k in range(count+1)]
    get = lambda arr,j:arr[j] if j>=0 else mp.mpf(0)
    A = mp.gamma(av)/((1+uv)*mp.gamma(av+1+uv))
    sac = 2*av+1
    quadratic = [-av*(sac+uv)/(uv*(1-uv)),-2*av/uv,mp.mpf(1)]
    x = av+1+uv
    b = 2/(uv*(1-uv*uv))
    c = 2*av/(uv*(1+uv))+sac/(uv*(1-uv))
    d = av*(sac+uv)/(uv*(1-uv*uv))
    cubic = [x*d,d+x*c,c+x*b,b]
    k_tail = mp.mpf(0)
    for j in range(count+1):
        cj = sum(quadratic[2-k]*get(cc,j-k) for k in range(3))
        dj = sum(cubic[3-k]*get(dd,j-k) for k in range(4))
        k_tail += A*cj*mp.zeta(uv+j,cutoff)
        k_tail += dj*mp.zeta(1+2*uv+j,cutoff)
    NN,M,S,S1 = finite_moments(av,mp.mpf(1),uv,{cutoff-1})[0]
    finite_Q = sum(counterterm(uv,av,mp.mpf(1),al,n) for n in range(cutoff))
    R = av*A
    beta = -(2*av+1)-(av+mp.mpf("1.5"))*uv-uv*uv/2
    T = A*(beta+al*uv)
    y = cutoff+al
    q_tail = (A*mp.zeta(uv,y)+(T-2*R/uv)*mp.zeta(1+uv,y)
              +2/(uv*(1-uv*uv))*mp.zeta(1+2*uv,y))
    return S-finite_Q+k_tail-q_tail


mp.mp.dps = 65
for av,uv,al in [(mp.mpf(".7"),mp.mpf(".2"),mp.mpf(".6")),
                 (mp.mpf("1.25"),mp.mpc(".12",".08"),mp.mpf("1.7"))]:
    approximate12 = accelerated_c1_series(av,uv,al,160,12)
    approximate16 = accelerated_c1_series(av,uv,al,160,16)
    exact = germ(uv,av,mp.mpf(1),al)
    report["accelerated_defining_series"].append({"a":s(av),"c":"1","u":s(uv),
       "alpha":s(al),"cutoff":160,"tail_order":16,"series_value":s(approximate16),
       "germ_value":s(exact),"absolute_error":s(abs(approximate16-exact)),
       "tail_order_12_to_16_change":s(abs(approximate16-approximate12)),
       "note":"Gamma-ratio tail truncation; diagnostic, not a certified interval."})


def harmonic_endpoint_tail(p, cutoff=100, count=16):
    H = mp.mpf(0)
    total = mp.mpf(0)
    for v in range(1,cutoff):
        H += mp.mpf(1)/v
        total += (1+mp.mpf(1)/(v+1)-H*(mp.mpf(1)/v+mp.mpf(1)/(v+1)))/v**p
    d = [mp.mpf(0),mp.mpf(2)]+[mp.mpf((-1)**(j-1)) for j in range(2,count+1)]
    hc = [mp.euler,mp.mpf(".5")]+[mp.mpf(0)]*(count-1)
    for j in range(2,count+1,2):
        hc[j] = -mp.bernoulli(j)/j
    for j in range(count+1):
        f = mp.mpf(1) if j==0 else mp.mpf((-1)**(j-1))
        f -= sum(hc[k]*d[j-k] for k in range(j+1))
        total += f*mp.zeta(p+j,cutoff)
        if d[j]:
            total += d[j]*mp.diff(lambda order:mp.zeta(order,cutoff),p+j)
    return total


Krat = lambda v:1+1/(v+1)-(mp.digamma(v+1)+mp.euler)*(1/v+1/(v+1))
z = mp.mpf(".5")
Gseries = mp.nsum(lambda v:Krat(v)*z**v,[1,mp.inf])
Gexact = 2*mp.log(2)-mp.log(2)**2-mp.pi**2/12
report["polylogarithmic_checks"].append({"identity":"G(1/2)","value":s(Gexact),
    "geometric_series_error":s(abs(Gseries-Gexact))})
for p,endpoint in [(2,3*mp.zeta(2)-2*mp.zeta(3)-mp.mpf("1.25")*mp.zeta(4)-1),
                   (3,1-2*mp.zeta(2)+4*mp.zeta(3)-mp.mpf("1.25")*mp.zeta(4)
                    +mp.zeta(2)*mp.zeta(3)-3*mp.zeta(5))]:
    approximate = harmonic_endpoint_tail(p)
    report["polylogarithmic_checks"].append({"identity":f"J_{p}","value":s(endpoint),
       "accelerated_series_error":s(abs(approximate-endpoint)),"cutoff":100,
       "harmonic_tail_order":16,"note":"Harmonic asymptotic tail diagnostic."})

assert all(report["symbolic"].values())
assert all(mp.mpf(row["D0_symmetric_error"])<mp.mpf("1e-24") and
           mp.mpf(row["D1_symmetric_error"])<mp.mpf("1e-24") for row in report["germ_jets"])
assert all(mp.mpf(row["exact_pearson_determinant_error"])<mp.mpf("1e-34")
           for row in report["finite_cutoffs"])
assert all(mp.mpf(row["absolute_error"])<mp.mpf("1e-27")
           for row in report["accelerated_defining_series"])
assert all(mp.mpf(row.get("geometric_series_error",row.get("accelerated_series_error")))
           <mp.mpf("1e-30") for row in report["polylogarithmic_checks"])
report["regression_thresholds_passed"] = True
OUT.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
