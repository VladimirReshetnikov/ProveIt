#!/usr/bin/env python3
"""Exploratory finite checks of the positive-filter proof.

Run: python check_filters.py [--no-zeta]
Requires mpmath. All checks are high-precision numerical checks, not interval
certificates. The paper's proof does not depend on this program.
"""
import argparse
import collections
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 65

def fmt(x, digits=18):
    return mp.nstr(x, digits)


def parameters(eta):
    M = int(mp.ceil(100 / eta))
    return M, M+1


def build_layers(positive, delta, eta):
    """Group a list of occurrences (including repeats) into phase-bin colors."""
    M, C = parameters(eta)
    bins = collections.defaultdict(list)
    for lam in sorted(positive):
        y = lam / delta
        k = int(mp.floor(y))
        j = int(mp.floor(M * (y-k)))
        assert k >= C and 0 <= j < M
        bins[j,k].append(lam)
    groups = collections.defaultdict(list)
    for (j,k), occurrences in bins.items():
        for color, lam in enumerate(occurrences):
            groups[j,color].append(lam)
    return groups


class PhaseFactor:
    def __init__(self, positive, delta, eta):
        self.positive = sorted(positive)
        self.delta, self.eta = delta, eta
        self.A = (mp.pi+eta)/delta
        self.freq = sorted(self.positive + [-x for x in self.positive])
        self.mat = mp.matrix([[self.base(lam-kap) for kap in self.freq]
                              for lam in self.freq])
        self.b = mp.matrix([self.base(lam) for lam in self.freq])
        self.a = mp.lu_solve(self.mat, -self.b)
        self.norm = mp.fsum(abs(x) for x in self.a)
        self.Z = 1 + mp.fsum(ai * self.base(lam)
                            for ai, lam in zip(self.a, self.freq))
        self.row = max(mp.fsum(abs(self.mat[i,j] - int(i==j))
                              for i in range(len(self.freq)))
                       for j in range(len(self.freq)))
        self.bnorm = mp.fsum(abs(x) for x in self.b)
        self.residual = max(abs(self(lam)) for lam in self.freq)
        assert self.row < mp.mpf('0.25')
        assert self.bnorm < mp.mpf('0.25')
        assert self.norm < mp.mpf(1)/3
        assert self.Z > 0
        assert self.residual < mp.mpf('1e-55')
        assert abs(self(0)-1) < mp.mpf('1e-55')
        assert max(abs(self.a[i]-self.a[len(self.a)-1-i]) for i in range(len(self.a))) < mp.mpf('1e-55')

    def base(self, x):
        return mp.sinc(mp.pi*x/self.delta) * mp.sinc(self.eta*x/self.delta)

    def __call__(self, x):
        return (self.base(x) + mp.fsum(ai*self.base(x-lam)
                                     for ai,lam in zip(self.a,self.freq))) / self.Z

    def report(self):
        return {
            'positive_frequencies': [fmt(x) for x in self.positive],
            'half_width': fmt(self.A),
            'matrix_off_diagonal_column_sum': fmt(self.row),
            'rhs_l1': fmt(self.bnorm),
            'correction_l1': fmt(self.norm),
            'unnormalized_density_multiplier_lower_bound': fmt(1-self.norm),
            'normalization': fmt(self.Z),
            'max_zero_residual': fmt(self.residual),
        }


def cheb(z, B, s):
    return mp.cos(s*mp.sqrt(z*z-B*B))/mp.cosh(s*B)


def lower_bound(positive_occurrences, B, L):
    return (L + 2*mp.fsum(mp.acosh(B/x) for x in positive_occurrences if x <= B))/B


def synthetic_checks():
    delta, eta = mp.mpf(10), mp.mpf('0.5')
    M,C = parameters(eta)
    # Rational frequencies; several nonadjacent cells and repeated occurrences.
    def freq(k,j,n):
        return delta*(k+(mp.mpf(j)+mp.mpf(n)/10)/M)
    positive = [freq(C+k,73,n) for k,n in [(0,1),(1,8),(3,4),(6,9),(9,2),(17,5)]]
    positive += [positive[0], positive[0], positive[2]]
    positive += [freq(C+k,11,n) for k,n in [(0,9),(2,1),(7,8),(13,3)]]
    groups=build_layers(positive,delta,eta)
    factors=[PhaseFactor(lams,delta,eta) for lams in groups.values()]
    # The transform of the convolution is their product. Check all required
    # derivative orders at each repeated zero; the exact reason is factorization.
    def product(z):
        return mp.fprod(f(z) for f in factors)
    mult = collections.Counter(positive)
    derivatives=[]
    for lam,m in sorted(mult.items()):
        vals=[abs(mp.diff(product,lam,j)) for j in range(m)]
        assert max(vals)<mp.mpf('1e-49')
        derivatives.append({'frequency':fmt(lam),'multiplicity':m,
                            'max_abs_derivative_through_order_m_minus_1':fmt(max(vals))})
    half_width=sum(f.A for f in factors)
    V=sum(f.A**2 for f in factors)
    for r in map(mp.mpf,['0','0.3','1','3']):
        val=mp.re(product(-1j*r))
        assert val <= mp.exp(V*r*r/2) + mp.mpf('1e-55')
    B = max(positive)+1
    L = mp.mpf(15)
    s = mp.acosh(mp.exp(L))/B
    lb=lower_bound(positive,B,L)
    assert half_width+s >= lb
    return {'eta':fmt(eta),'delta':fmt(delta),'M':M,'C':C,'occurrences':len(positive),
            'distinct_frequencies':len(mult),'number_of_factors':len(factors),
            'factors':[f.report() for f in factors], 'multiplicity_checks':derivatives,
            'cancellation_half_width':fmt(half_width), 'cancellation_variance_proxy':fmt(V),
            'combined_half_width':fmt(half_width+s),'slit_lower_bound':fmt(lb),
            'B':fmt(B),'L':fmt(L)}


def cheb_checks():
    B=mp.mpf(7); L=mp.mpf(12); s=mp.acosh(mp.exp(L))/B
    sup=mp.exp(-L)
    assert abs(cheb(0,B,s)-1) < mp.mpf('1e-55')
    assert abs(cheb(B,B,s)-sup) < mp.mpf('1e-55')
    observed=max(abs(cheb(B+mp.mpf(j)/10,B,s)) for j in range(501))
    assert observed <= sup+mp.mpf('1e-55')
    vals=[]
    for r in map(mp.mpf,['0','0.25','0.5','1','2','10']):
        mgf=mp.re(cheb(-1j*r,B,s)); ub=mp.exp(s*r*r/(2*B))
        assert mgf <= ub+mp.mpf('1e-55')
        vals.append({'r':fmt(r),'mgf':fmt(mgf),'subgaussian_upper_bound':fmt(ub)})
    return {'B':fmt(B),'L':fmt(L),'optimal_half_width':fmt(s),'exact_tail_bound':fmt(sup),
            'sampled_tail_max':fmt(observed),'moment_checks':vals}


def zeta_checks():
    B=mp.mpf(60); L=B*mp.log(B)*(-mp.log(mp.sin(1)))
    n=int(mp.nzeros(B))
    pos=[mp.im(mp.zetazero(k)) for k in range(1,n+1)]
    assert all(0<x<=B for x in pos)
    circular=mp.pi/B*mp.fsum(mp.log(B/x) for x in pos)
    slit=lower_bound(pos,B,mp.mpf(0))
    assert slit >= circular
    # The finite explicit convolution is feasible at these *sampled* ordinates.
    simple_width=mp.fsum(mp.pi/(2*x) for x in pos)+mp.acosh(mp.exp(L))/B
    combined_lower=lower_bound(pos,B,L)
    assert simple_width>=combined_lower
    return {'warning':'mpmath approximations to ordinates, not certified zero data; no asymptotic claim from this finite sample',
            'B':fmt(B),'number_of_positive_ordinates':n,'positive_ordinates':[fmt(x) for x in pos],
            'circular_Jensen_lower_half_width':fmt(circular),
            'slit_lower_half_width_without_tail':fmt(slit),
            'L':fmt(L),'slit_lower_half_width_with_tail':fmt(combined_lower),
            'simple_bernoulli_plus_cheb_feasible_half_width':fmt(simple_width),
            'asymptotic_leading_coefficient_with_article_tail':fmt(mp.mpf('0.5')-mp.log(mp.sin(1)))}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-zeta',action='store_true')
    args=parser.parse_args()
    result={'status':'all numerical assertions passed','precision_decimal_digits':mp.mp.dps,
            'synthetic_near_lattice':synthetic_checks(),'pure_stopband':cheb_checks()}
    if not args.no_zeta: result['zeta_example']=zeta_checks()
    out=Path(__file__).with_name('numerical_checks.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS:',out.name)

if __name__=='__main__': main()
