#!/usr/bin/env python3
"""Independent floating-point diagnostics for ordered Hurwitz finite parts.

Finite sums are combined with Euler--Maclaurin tails of the outer and
inner Hurwitz factors.  Cauchy coefficient extraction is independent of
the canonical-germ formula being checked.  These are not interval proofs.
"""
import argparse
import json
from functools import lru_cache
import mpmath as mp


@lru_cache(maxsize=None)
def em_constants(order):
    return tuple(mp.bernoulli(2*k)/mp.factorial(2*k)
                 for k in range(1, order+1))


def hurwitz_tail_terms(s, order, plus):
    r = {-1: 1/(s-1), 0: mp.mpf('0.5') if plus else mp.mpf('-0.5')}
    for k, b in enumerate(em_constants(order), 1):
        r[2*k-1] = b*mp.rf(s, 2*k-1)
    return r


def z2(s, t, a, cutoff=30, order=18):
    total = sum(mp.zeta(s, n+a+1)/(n+a)**t for n in range(cutoff))
    tail = hurwitz_tail_terms(s, order, False)
    return total + sum(c*mp.zeta(s+t+h, cutoff+a) for h, c in tail.items())


def z3(s, t, v, a, cutoff=30, order=18):
    total = 0
    harmonic = 0
    for n in range(cutoff):
        x = n+a
        total += mp.zeta(s, x+1)*harmonic/x**t
        harmonic += x**(-v)
    outer = hurwitz_tail_terms(s, order, False)
    inner = hurwitz_tail_terms(v, order, True)
    convolution = {}
    for h, c in outer.items():
        for k, d in inner.items():
            convolution[h+k] = convolution.get(h+k, 0) + c*d
    total += mp.zeta(v, a)*sum(c*mp.zeta(s+t+h, cutoff+a)
                                  for h, c in outer.items())
    total -= sum(c*mp.zeta(s+t+v+h, cutoff+a)
                 for h, c in convolution.items())
    return total


def cauchy(f, power=0, radius=None, points=24):
    # Midpoint angular nodes avoid landing on a real special parameter.
    if radius is None:
        radius = mp.mpf('0.008')
    vals = []
    for j in range(points):
        eps = radius*mp.exp(2j*mp.pi*(j+mp.mpf('0.5'))/points)
        vals.append(f(eps)/eps**power)
    return sum(vals)/points


def eta_mellin_a1():
    def integrand(t):
        # -log(1-exp(-t))/(exp(t)-1) has the singular part -log(t)/t.
        k = -mp.log(-mp.expm1(-t))/mp.expm1(t)
        if t < 1:
            k += mp.log(t)/t
        return mp.log(t)*k
    j = mp.quad(integrand, [0, mp.mpf('0.25'), 1, 2, 4, 8, 16, 64, mp.inf])
    return j+mp.euler**3/6-mp.euler*mp.zeta(2)/2+mp.zeta(3)/3


def triple_formula(a, c, eta):
    p, q, r = c
    g = [mp.stieltjes(j, a) for j in range(3)]
    b3 = (g[0]**3-3*g[0]*mp.zeta(2,a)+2*mp.zeta(3,a))/6
    return (b3-r/p*(g[0]*g[1]+mp.diff(lambda s:mp.zeta(s,a),2))
            +r*r*g[2]/(2*p*(p+q))+(q-r)*eta/p)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dps', type=int, default=50)
    ap.add_argument('--points', type=int, default=20)
    ap.add_argument('--cutoff', type=int, default=36)
    ap.add_argument('--order', type=int, default=20)
    ap.add_argument('--guard-dps', type=int, default=40)
    ap.add_argument('--tolerance', default='1e-32')
    ap.add_argument('--quick', action='store_true')
    args=ap.parse_args()
    if min(args.dps,args.points,args.cutoff,args.order) <= 0 or args.guard_dps < 0:
        ap.error('precision, node count, cutoff, and order must be positive; guard digits cannot be negative')
    mp.mp.dps=args.dps
    options={'cutoff':args.cutoff,'order':args.order}
    nstr=lambda x:mp.nstr(x, args.dps-5)
    out={'precision_dps':args.dps,'cauchy_points':args.points,
         'cutoff':args.cutoff,'em_order':args.order,'triple_guard_dps':args.guard_dps,
         'diagnostic_tolerance':args.tolerance,'checks':[],
         'status':'floating-point diagnostics; no interval certification'}
    residuals=[]
    shifts=[mp.mpf(1)] if args.quick else [mp.mpf(1),mp.mpf('0.75')]
    for a in shifts:
        eta=cauchy(lambda eps:z2(1+eps,1,a,**options), power=1, points=args.points)
        out['checks'].append({'name':'eta_strict_harmonic','a':str(a),
                              'value':nstr(eta)})
        if a==1:
            integ=eta_mellin_a1()
            residuals.append(abs(eta-integ))
            out['checks'].append({'name':'eta_Mellin_comparison','value':nstr(integ),
                                  'residual':nstr(abs(eta-integ))})
        slopes=[(1,mp.mpf('0.5'),mp.mpf('0.5')),
                (mp.mpf('1.25'),mp.mpf('0.5'),mp.mpf('0.75'))]
        for c in slopes:
            def direct_triple(eps):
                # Some tiny integer-shift Hurwitz values have an absolute
                # roundoff floor. Large EM convolution coefficients amplify
                # it, so guard precision is needed before multiplication.
                with mp.extradps(args.guard_dps):
                    return z3(1+c[0]*eps,1+c[1]*eps,1+c[2]*eps,a,**options)
            fp=cauchy(direct_triple, points=args.points)
            expected=triple_formula(a,c,eta)
            residuals.append(abs(fp-expected))
            out['checks'].append({'name':'ordered_depth_three', 'a':str(a),
                                  'slopes':[str(x) for x in c], 'direct':nstr(fp),
                                  'formula':nstr(expected), 'residual':nstr(abs(fp-expected))})
    out['maximum_comparison_residual']=nstr(max(residuals))
    out['diagnostic_passed']=bool(max(residuals)<mp.mpf(args.tolerance))
    print(json.dumps(out, indent=2))
    if not out['diagnostic_passed']:
        raise SystemExit('Numerical residual exceeded the stated diagnostic tolerance.')


if __name__=='__main__':
    main()
