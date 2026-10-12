#!/usr/bin/env python3
"""Independent numerical diagnostics for independent_shifts.tex.

The written proofs establish the theorems.  These high-precision tests are
diagnostics, not interval certificates.  The product generator is compared
with a direct quadrature of two Hurwitz functions.  The explicit digamma,
Wronskian, and trigamma identities are compared with direct polygamma
quadratures.  All output is local to this directory.
"""
from __future__ import annotations

import json
from pathlib import Path
import mpmath as mp
import sympy as sp

mp.mp.dps = 65
BASE = Path(__file__).resolve().parents[1]/'results'
records: list[dict] = []


def record(name, lhs, rhs, tol="1e-54", **extra):
    err = abs(lhs - rhs)
    scale = max(1, abs(lhs), abs(rhs))
    passed = err / scale < mp.mpf(tol)
    records.append({"name": name, "lhs": str(lhs), "rhs": str(rhs),
                    "absolute_error": mp.nstr(err, 12),
                    "relative_error": mp.nstr(err / scale, 12),
                    "passed": bool(passed), **extra})
    if not passed:
        raise AssertionError(records[-1])


def zreg(u, c):
    if u == 0:
        return -mp.digamma(c)
    return mp.zeta(1 + u, c) - 1 / u


def zreg_prime(u, c):
    if u == 0:
        return -mp.stieltjes(1, c)
    return mp.diff(lambda s: mp.zeta(s, c), 1 + u) + 1 / u**2


def Q(u, v):
    return mp.gamma(1 + u + v) / (mp.gamma(1 + u) * mp.gamma(1 + v))


def E(u):
    return mp.pi * u / mp.sin(mp.pi * u) if u else mp.mpf(1)


def universal_T(u, v):
    if u == 0 and v == 0:
        return -2 * mp.zeta(2)
    if u == 0:
        return -(mp.digamma(1 + v) + mp.euler + (E(v) - 1) / v) / v
    if v == 0:
        return universal_T(v, u)
    if u + v == 0:
        return mp.pi * mp.cot(mp.pi * u) / u - 1 / u**2
    return (u + v - Q(u, v) * (u * E(v) + v * E(u))) / (u * v * (u + v))


def beta_kernel(s, t, a, b):
    if a == b:
        return a**(1-s-t) / (s+t-1)
    return b**(1-s-t) * mp.hyp2f1(s, s+t-1, s+t, 1-a/b) / (s+t-1)


def accelerated_V(u, v, c, z, terms=90):
    # The test cutoffs ensure |z|/Re(c)<1/8, so this truncation is well
    # beyond the working precision for these fixed test cases.
    ratio = mp.mpf(1)
    zpow = z**(-v)
    total = mp.mpf(0)
    for j in range(1, terms + 1):
        ratio *= (u + j) / j
        zpow *= -z
        total -= ratio * zpow * mp.zeta(1 + u + j, c) / (j - v)
    return total


def make_cutoffs(a, b):
    k = max(0, int(mp.ceil(8 * abs(b) - mp.re(a) + mp.re(b))) + 1)
    l = max(1, int(mp.ceil(8 * abs(a) - mp.re(b) + mp.re(a))) + 1)
    return k, l


def completed_master(u, v, a, b, k=None, l=None):
    if k is None:
        k, l = make_cutoffs(a, b)
    c, d = k + a - b, l + b - a
    out = sum(beta_kernel(1+u, 1+v, a+j, b) for j in range(k))
    out += sum(beta_kernel(1+u, 1+v, a, b+j) for j in range(1, l))
    out += universal_T(u, v)
    if v:
        out += (b**(-v) * zreg(u, c) - Q(u, v)*E(v)*zreg(u+v, c)) / v
    else:
        out += -(mp.log(b)+mp.digamma(1+u)+mp.euler)*zreg(u, c)-zreg_prime(u, c)
    if u:
        out += (a**(-u) * zreg(v, d) - Q(u, v)*E(u)*zreg(u+v, d)) / u
    else:
        out += -(mp.log(a)+mp.digamma(1+v)+mp.euler)*zreg(v, d)-zreg_prime(v, d)
    return out + accelerated_V(u, v, c, b) + accelerated_V(v, u, d, a)


def logarithmic_L(p, c, z):
    shift = max(0, int(mp.ceil(8*abs(z)-mp.re(c))) + 1)
    out = sum(mp.log1p(z/(n+c))/(n+c)**p for n in range(shift))
    tailc = c + shift
    out -= sum((-z)**j * mp.zeta(p+j, tailc) / j for j in range(1, 91))
    return out


def D(a, b):
    return mp.log(a/b)/(a-b) if a != b else 1/a


def W0(a, b):
    return (2*mp.log(a/b)-(a-b)*(1/a+1/b))/(a-b)**2 if a != b else mp.mpf(0)


def positive_cutoffs(a, b):
    return max(1, int(mp.ceil(b-a))+1), max(1, int(mp.ceil(a-b))+1)


def stieltjes_digamma_product(a, b):
    k, l = make_cutoffs(a, b)
    c, d = k+a-b, l+b-a
    def first_prefix(A, B):
        if A == B:
            return -(mp.log(A)+1)/A
        return -(mp.log(A/B)*mp.log(A)+mp.polylog(2,1-B/A))/(A-B)
    out = sum(first_prefix(a+j,b) for j in range(k))
    out += sum(first_prefix(a,b+j) for j in range(1,l))
    out += (mp.zeta(3)-mp.stieltjes(2,c)-mp.stieltjes(2,d)/2
            +mp.log(b)*mp.stieltjes(1,c)+mp.zeta(2)*mp.digamma(c)
            +(mp.zeta(2)-mp.log(a)**2/2)*mp.digamma(d))
    for j in range(1,91):
        out -= (-b)**j/j*(mp.harmonic(j)*mp.zeta(j+1,c)
                          +mp.diff(lambda s:mp.zeta(s,c),j+1))
        out -= (-a)**j/j*(1/mp.mpf(j)-mp.log(a))*mp.zeta(j+1,d)
    return out


def digamma_product(a, b, k=None, l=None):
    if k is None:
        k, l = positive_cutoffs(a, b)
    c, d = k+a-b, l+b-a
    out = sum(D(a+n,b) for n in range(k))+sum(D(a,b+n) for n in range(1,l))
    return (out + mp.stieltjes(1,c)+mp.stieltjes(1,d)-2*mp.zeta(2)
            +mp.log(b)*mp.digamma(c)+mp.log(a)*mp.digamma(d)
            +logarithmic_L(1,c,b)+logarithmic_L(1,d,a))


def wronskian(a, b, k=None, l=None):
    if k is None:
        k, l = positive_cutoffs(a,b)
    c,d=k+a-b,l+b-a
    out=sum(W0(a+n,b) for n in range(k))+sum(W0(a,b+n) for n in range(1,l))
    zp=lambda z:mp.diff(lambda s:mp.zeta(s,z),2)
    out+=2*(zp(d)-zp(c)+mp.log(a)*mp.zeta(2,d)-mp.log(b)*mp.zeta(2,c)
           +logarithmic_L(2,c,b)-logarithmic_L(2,d,a))
    return out+(2*mp.digamma(c)-mp.digamma(k+a))/b+(mp.digamma(l+b)-2*mp.digamma(d))/a


def main():
    for j, (a,b,u,v) in enumerate([
        (mp.mpf('.7'),mp.mpf('1.1'),mp.mpf('.2'),mp.mpf('.3')),
        (mp.mpf('.4'),mp.mpf('.6'),mp.mpf('-.12'),mp.mpf('.09')),
        (mp.mpf('.7'),mp.mpf('1.1'),mp.mpf('.12'),mp.mpf('-.12')),
        (mp.mpf('.7'),mp.mpf('1.1'),mp.mpf(0),mp.mpf('.08')),
        (mp.mpf('.7'),mp.mpf('1.1'),mp.mpf('.08'),mp.mpf(0)),
        (mp.mpf('.7'),mp.mpf('1.1'),mp.mpf(0),mp.mpf(0)),
        (mp.mpc('.7','.2'),mp.mpc('1.1','-.15'),mp.mpc('.08','.03'),mp.mpc('-.04','.02')),
    ]):
        direct=mp.quad(lambda x:zreg(u,a+x)*zreg(v,b+x),[0,1])
        record(f'completed_generator_{j}',direct,completed_master(u,v,a,b))

    # Two entirely different finite prefixes must give the same germ.
    a,b,u,v=map(mp.mpf,('.7','1.1','.03','-.04'))
    k,l=make_cutoffs(a,b)
    record('cutoff_invariance_generator',completed_master(u,v,a,b,k,l),
           completed_master(u,v,a,b,k+2,l+3))

    a,b=mp.mpf('.7'),mp.mpf('1.1')
    direct=mp.quad(lambda x:mp.stieltjes(1,a+x)*mp.digamma(b+x),[0,1])
    record('first_stieltjes_digamma',direct,stieltjes_digamma_product(a,b))

    for j,(a,b) in enumerate([(mp.mpf('.4'),mp.mpf('.6')),
                              (mp.mpf('.5'),mp.mpf('.5')),
                              (mp.mpf('.7'),mp.mpf('1.1')),
                              (mp.mpf('.3'),mp.mpf('3.7')),
                              (mp.mpf('2.8'),mp.mpf('.2'))]):
        direct=mp.quad(lambda x:mp.digamma(a+x)*mp.digamma(b+x),[0,1])
        record(f'digamma_product_{j}',direct,digamma_product(a,b))
        directw=mp.quad(lambda x:mp.digamma(a+x)*mp.polygamma(1,b+x)
                       -mp.polygamma(1,a+x)*mp.digamma(b+x),[0,1])
        record(f'antisymmetric_first_derivative_{j}',directw,wronskian(a,b))
        k,l=positive_cutoffs(a,b)
        record(f'cutoff_invariance_digamma_{j}',digamma_product(a,b,k,l),
               digamma_product(a,b,k+1,l+2))
        record(f'antisymmetry_{j}',wronskian(a,b),-wronskian(b,a))

    for j,a in enumerate(map(mp.mpf,('.3','1','2'))):
        rhs=(1/(3*a**3)+4*mp.diff(mp.zeta,3)+4*mp.zeta(2)/a
             +4*mp.zeta(3)*mp.log(a)-2*(mp.digamma(1+a)+mp.euler)/a**2
             -4*logarithmic_L(3,1,a))
        direct=mp.quad(lambda x:mp.polygamma(1,x)**2,[a,a+1])
        record(f'trigamma_square_{j}',direct,rhs)

    # The finite prefix has explicitly dilogarithmic first spectral jets.
    a,b=mp.mpf('1.7'),mp.mpf('.8')
    ell=mp.log(a/b)
    rhsu=-(ell*mp.log(a)+mp.polylog(2,1-b/a))/(a-b)
    rhsv=rhsu+ell**2/(2*(a-b))
    directu=-mp.quad(lambda x:mp.log(x+a)/((x+a)*(x+b)),[0,mp.inf])
    directv=-mp.quad(lambda x:mp.log(x+b)/((x+a)*(x+b)),[0,mp.inf])
    record('dilogarithmic_prefix_u',directu,rhsu)
    record('dilogarithmic_prefix_v',directv,rhsv)

    # Verify each logarithmic-family differential rule independently against
    # the rational/digamma expression, using a direct series derivative.
    c,z=mp.mpf('.8'),mp.mpf('1.2')
    for p in range(1,5):
        rp=mp.nsum(lambda n:1/((n+c)**p*(n+c+z)),[0,mp.inf])
        finite=(mp.digamma(c+z)-mp.digamma(c))/z
        for q in range(2,p+1):
            finite=(mp.zeta(q,c)-finite)/z
        record(f'logarithmic_R_{p}',rp,finite)
        dc=mp.nsum(lambda n:-p*mp.log1p(z/(n+c))/(n+c)**(p+1)
                   -z/((n+c)**(p+1)*(n+c+z)),[0,mp.inf])
        record(f'logarithmic_c_derivative_{p}',dc,
               -p*logarithmic_L(p+1,c,z)+finite-mp.zeta(p+1,c))

    # Exact polynomial checks for the removable universal Gamma quotient.
    u,v=sp.symbols('u v')
    exact=0
    for h in range(1,15):
        poly=sum((-1)**j*u**(2*h-2-j)*v**j for j in range(2*h-1))
        assert sp.expand((u+v)*poly-(u**(2*h-1)+v**(2*h-1)))==0
        exact+=1
    # These are exact local cancellation checks, not arithmetic independence
    # assertions about evaluated special functions.
    z2,z3,z4=sp.symbols('zeta2 zeta3 zeta4')
    logq=z2*u*v-z3*(u*u*v+u*v*v)+z4*(u**3*v+sp.Rational(3,2)*u*u*v*v+u*v**3)
    assert sp.rem(sp.Poly(logq,u),sp.Poly(u,u))==0
    assert sp.rem(sp.Poly(logq,v),sp.Poly(v,v))==0
    exact+=2

    report={"working_decimal_precision":mp.mp.dps,
            "numerical_checks":len(records),"exact_polynomial_checks":exact,
            "all_passed":all(r['passed'] for r in records),
            "maximum_absolute_error":max((mp.mpf(r['absolute_error']) for r in records)),
            "scope":"Numerical diagnostics plus exact polynomial cancellation; not interval certification.",
            "checks":records}
    report['maximum_absolute_error']=mp.nstr(report['maximum_absolute_error'],12)
    (BASE/'verification_independent_shifts.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))


if __name__=='__main__':
    main()
