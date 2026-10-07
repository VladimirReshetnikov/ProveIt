#!/usr/bin/env python3
"""High-precision direct recurrence fixtures, rare parity and CF checks.

Analytic outside-window bounds are evaluated with mpmath. Neither those displayed
bounds nor the remaining floating-point operations are interval-certified.
This is numerical corroboration, not a proof of the asymptotic theorem.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import mpmath as mp
from common import emit, integer, new_file_path, require
DEFAULT_NS = (10000,10001,1000000,1000001,100000000,100000001)


def fmt(value):
    return mp.nstr(value, 28)


def parameters(n):
    integer(n, 10000, 10000000001, 'numerical n')
    N = mp.mpf(n); t = 1/mp.sqrt(N); A = mp.mpf(3)/4; c = mp.sqrt(mp.e/2)
    lam = c/t
    mu = N/(2*A)*mp.lambertw(2*A*lam/N*mp.exp(1/(4*N)))
    mean = lam-mp.mpf(3)/2*c*c+(c/4+33*c**3/8)*t+(15*c*c/8-44*c**4/3)*t*t
    var = lam-3*c*c+(c/4+99*c**3/8)*t+(15*c*c/4-176*c**4/3)*t*t
    require(0 < var < mean, 'moment parameters not positive')
    M = int(mp.floor(mean*mean/(mean-var)+mp.mpf('0.5')))
    M0 = int(mp.floor(2*N/3+mp.mpf('0.5')))
    tuned = mean+mp.mpf(5)/8*(2*mp.log(2)-3)*mu*mu/(N*N)
    require(0 < tuned < mean < M and mu < M0, 'invalid binomial parameters')
    return N,A,c,lam,mu,mean,var,M0,M,tuned


def poisson_logmass(r, nu, a):
    return -nu+r*mp.log(nu)-mp.loggamma(r+1)+mp.log(2)-mp.log1p((-1)**a*mp.exp(-2*nu))


def binomial_logmass(r, M, nu, a):
    require(0 <= r <= M and 0 < nu < M, 'invalid binomial mass parameters')
    p = nu/M
    return (mp.loggamma(M+1)-mp.loggamma(r+1)-mp.loggamma(M-r+1)
            +r*mp.log(p)+(M-r)*mp.log1p(-p)+mp.log(2)
            -mp.log1p((-1)**a*(1-2*p)**M))


def ordinary_chernoff(nu, lo, hi):
    require(lo <= nu <= hi, 'Chernoff window does not contain mean')
    value = mp.mpf(0)
    if lo > 1:
        x = mp.mpf(lo-1)
        value += mp.exp(-nu+x-x*mp.log(x/nu))
    elif lo == 1:
        value += mp.exp(-nu)
    x = mp.mpf(hi+1)
    value += mp.exp(-nu+x-x*mp.log(x/nu))
    return value


def numerical_case(n, digits=80):
    integer(digits, 60, 120, 'digits')
    with mp.workdps(digits):
        N,A,c,lam,mu,mean,var,M0,M,tuned = parameters(n)
        a = n%2
        radius = 18*mp.sqrt(lam)+100
        lo = max(0,int(mp.floor(lam-radius))); lo += (n-lo)%2
        hi = min(n,int(mp.ceil(lam+radius))); hi -= (hi-n)%2
        rs = list(range(lo,hi+1,2))
        r0 = int(mp.floor(mu)); r0 += (n-r0)%2
        require(lo <= r0 <= hi and hi <= min(M0,M,n), 'recurrence window invalid')
        index = (r0-lo)//2
        weights = [mp.mpf(0)]*len(rs); weights[index] = 1
        def ratio(rr):
            k = (n-rr)//2; m = (n+rr)//2
            return k*mp.exp(k*mp.log1p(1/mp.mpf(m)))/((rr+1)*(rr+2))
        for i in range(index+1,len(rs)):
            weights[i] = weights[i-1]*ratio(rs[i-1])
        for i in range(index-1,-1,-1):
            weights[i] = weights[i+1]/ratio(rs[i])
        normal = mp.fsum(weights)
        P = [w/normal for w in weights]
        # The exact finite-law tail follows from Delta <= 1/(4n), divided
        # by a positive *truncated* normalizer, not an asymptotic normalizer.
        k0 = (n-r0)//2; m0 = (n+r0)//2
        logW = k0*mp.log(m0)+mp.loggamma(m0+1)-mp.loggamma(k0+1)-mp.loggamma(r0+1)
        delta0 = logW-N/2*mp.log(N/2)-r0*mp.log(lam)+mp.loggamma(r0+1)
        Ntrunc = mp.exp(poisson_logmass(r0,lam,a)+delta0)*normal
        require(Ntrunc > 0, 'nonpositive exact truncated normalizer')
        exact_tail = (mp.exp(1/(4*N))*2*ordinary_chernoff(lam,lo,hi)
                      / ((1+(-1)**a*mp.exp(-2*lam))*Ntrunc))
        gamma = mp.mpf(5)/8
        phi = lambda x: mp.exp(-x*x/2)/mp.sqrt(2*mp.pi)
        matched_constant = gamma/2*(2*phi(0)+8*phi(mp.sqrt(3)))
        tuned_constant = gamma*mp.log(2)*mp.sqrt(2/mp.pi)
        laws = [('original_poisson',0,lam,A*mp.sqrt(2/mp.pi)*lam**mp.mpf('1.5')/N),
                ('tilted_poisson',0,mu,A*mp.sqrt(2/(mp.pi*mp.e))*mu/N),
                ('fixed_trials',M0,mu,mp.mpf(3)/8*mp.sqrt(2/mp.pi)*mu**mp.mpf('2.5')/(N*N)),
                ('mean_corrected',M0,mu+mp.mpf(3)/4*mu**3/(N*N),mp.mpf(15)/4*phi(1)*mu**2/(N*N)),
                ('moment_matched',M,mean,matched_constant*mu**mp.mpf('1.5')/(N*N)),
                ('TV_tuned',M,tuned,tuned_constant*mu**mp.mpf('1.5')/(N*N))]
        rows = {}; refs = {}
        for name,m,nu,scale in laws:
            Q = [mp.exp(binomial_logmass(lo,m,nu,a) if m else poisson_logmass(lo,nu,a))]
            for rr in rs[:-1]:
                qratio = ((m-rr)*(m-rr-1)*(nu/(m-nu))**2 if m else nu*nu)/((rr+1)*(rr+2))
                Q.append(Q[-1]*qratio)
            parity = (1+(-1)**a*((1-2*nu/m)**m if m else mp.exp(-2*nu)))/2
            tail = ordinary_chernoff(nu,lo,hi)/parity
            require(abs(mp.fsum(Q)-1) < tail+mp.mpf(10)**(-(digits-18)), 'reference normalization mismatch')
            distance = mp.fsum(abs(p-q) for p,q in zip(P,Q))/2
            rows[name] = {'TV_window_estimate': fmt(distance), 'ratio_to_sharp_equivalent': fmt(distance/scale),
                          'reference_tail_bound_evaluated': fmt(tail),
                          'TV_truncation_error_bound_evaluated': fmt(exact_tail+tail/2),
                          'unconditioned_mean': fmt(nu)}
            if m:
                rows[name]['trials'] = m
            refs[name] = Q
        mean_shift = mp.fsum((rr-mu)*p for rr,p in zip(rs,P))
        variance = mp.fsum((rr-mu)**2*p for rr,p in zip(rs,P))-mean_shift**2
        density_remainders = {}
        for name,alpha in [('moment_matched',mp.mpf(0)),('TV_tuned',2*mp.log(2)-3)]:
            terms = []
            for rr,p,q0,qb in zip(rs,P,refs['tilted_poisson'],refs[name]):
                y = rr-mu
                C3 = y**3-3*y*y+(2-3*mu)*y+2*mu
                terms.append(abs(p-qb-q0*gamma/(N*N)*(C3-alpha*mu*y)))
            density_remainders[name] = fmt(mp.fsum(terms)*N**mp.mpf('1.5'))
        return {'n':n, 'parity':a, 'digits':digits, 'lambda':fmt(lam), 'mu':fmt(mu),
                'window':[lo,hi], 'window_points':len(rs),
                'variance_approximation_order': 'through t^2',
                'exact_truncated_normalizer':fmt(Ntrunc), 'exact_law_tail_bound_evaluated':fmt(exact_tail),
                'mean_window':fmt(mu+mean_shift), 'variance_window':fmt(variance),
                'mean_residual_ratio':fmt(mean_shift/(mu**3/(N*N))),
                'variance_residual_ratio':fmt((variance-mu+2*A*mu**2/N)/(mu**3/(N*N))),
                'laws':rows, 'window_L1_density_remainder_times_n_3_over_2':density_remainders}


def rare_parity():
    with mp.workdps(90):
        cases = 0; max_mean = mp.mpf(0); max_variance = mp.mpf(0); max_atom = mp.mpf(0)
        ps = [mp.mpf(x) for x in ('0','1e-30','1e-12','.001','.01','.1','.3','.5','.7','.9')]
        ps += [1-mp.mpf('1e-12'),1-mp.mpf('1e-30'),mp.mpf(1)]
        for M in [0,1,2,3,5,10,30,100,500]:
            for p in ps:
                nu = M*p; v = nu*(1-p); z = 1-2*p
                weights = [mp.binomial(M,r)*p**r*(1-p)**(M-r) for r in range(M+1)]
                if M >= 2:
                    signed1 = mp.fsum((r-nu)*(-1)**r*w for r,w in enumerate(weights))
                    signed2 = mp.fsum((r-nu)**2*(-1)**r*w for r,w in enumerate(weights))
                    require(abs(signed1+2*v*z**(M-1)) < mp.mpf('1e-70'), 'signed first moment check')
                    require(abs(signed2-v*(4*v-1)*z**(M-2)) < mp.mpf('1e-65'), 'signed second moment check')
                for a in (0,1):
                    total = mp.fsum(weights[a::2])
                    if total == 0:
                        continue  # Undefined conditioning events are not distributions.
                    mean = mp.fsum(r*weights[r]/total for r in range(a,M+1,2))
                    var = mp.fsum((r-mean)**2*weights[r]/total for r in range(a,M+1,2))
                    atom = max(weights[a::2])/total
                    require(abs(mean-nu) <= 1+mp.mpf('1e-70'), 'mean displacement bound')
                    require(var <= 8*(v+1), 'variance bound')
                    require(atom*mp.sqrt(v+1) <= 3, 'atom check')
                    max_mean = max(max_mean,abs(mean-nu)); max_variance = max(max_variance,var/(v+1))
                    max_atom = max(max_atom,atom*mp.sqrt(v+1)); cases += 1
        require(cases == 205, 'rare parity case count changed')
        return {'finite_mass_cases':cases, 'digits':90, 'max_mean_displacement':fmt(max_mean),
                'max_variance_over_v_plus_1':fmt(max_variance), 'max_atom_times_sqrt_v_plus_1':fmt(max_atom),
                'scope':'Finite endpoint/rare-parity corroboration; the article supplies uniform bounds.'}


def cf_map(nu, v, mu, nu0, a, derivatives=False):
    require(0 < v < nu and mu > 0, 'CF parameters require 0 < v < nu and mu > 0')
    p = 1-v/nu; angle = 1/mp.sqrt(mu); sigma = (-1)**a
    def root(w):
        f = mp.log1p(p*w)/p
        fp = (p*w/(1+p*w)-mp.log1p(p*w))/(p*p)
        value = mp.exp(nu*f)
        return value, value*(f+(1-p)*fp), -value*fp
    first = root(mp.expm1(1j*angle))
    second = root(-1-mp.exp(1j*angle))
    denominator = root(-2)
    num = first[0]+sigma*second[0]; den = 1+sigma*denominator[0]
    center = mp.exp(-1j*angle*nu0)
    value = center*num/den
    if not derivatives:
        return value
    dx = center*((first[1]+sigma*second[1])*den-num*sigma*denominator[1])/(den*den)
    dy = center*((first[2]+sigma*second[2])*den-num*sigma*denominator[2])/(den*den)
    return value,dx,dy


def jacobian_checks():
    with mp.workdps(90):
        rows = []
        for n in [10000,10001,1000000,1000001,10000000000,10000000001]:
            N,A,c,lam,mu,mean,var,M0,M,tuned = parameters(n)
            # The moment-matched baseline uses its actual rounded binomial variance.
            v0 = mean*(1-mean/M); a = n%2
            value, dnu, dv = cf_map(mean,v0,mu,mean,a,True)
            ndnu = mp.diff(lambda nu:cf_map(nu,v0,mu,mean,a),mean)
            ndv = mp.diff(lambda v:cf_map(mean,v,mu,mean,a),v0)
            require(abs(dnu-ndnu) < mp.mpf('1e-65') and abs(dv-ndv) < mp.mpf('1e-65'),
                    'analytic CF derivatives differ from numerical differentiation')
            dx = mp.sqrt(mu)*dnu; dy = mu*dv
            trace = abs(dx)**2+abs(dy)**2
            determinant = mp.re(dx)*mp.im(dy)-mp.im(dx)*mp.re(dy)
            smallest = mp.sqrt((trace-mp.sqrt(trace*trace-4*determinant**2))/2)
            eps = mu**mp.mpf('1.5')/(N*N)
            diff = cf_map(mean+2*eps*mp.sqrt(mu),v0-3*eps*mu,mu,mean,a)-value
            ratio = abs(diff)/(eps*mp.sqrt(13))
            require(smallest > mp.mpf('.25'), 'Jacobian minimum singular value')
            require(ratio > mp.mpf('.3'), 'fine displacement lower bound')
            rows.append({'n':n, 'dx_real_imag':[fmt(mp.re(dx)),fmt(mp.im(dx))],
                         'dy_real_imag':[fmt(mp.re(dy)),fmt(mp.im(dy))],
                         'minimum_singular_value':fmt(smallest), 'epsilon_scale_inverse_ratio':fmt(ratio)})
        return rows


def run(ns=DEFAULT_NS, digits=80):
    integer(digits, 60, 120, 'digits')
    require(1 <= len(ns) <= 12, 'choose 1 to 12 numerical n values')
    for n in ns:
        integer(n,10000,10000000001,'numerical n')
    with mp.workdps(80):
        constants = {'matched':fmt(mp.mpf(5)/16*mp.sqrt(2/mp.pi)*(1+4*mp.exp(-mp.mpf(3)/2))),
                     'optimal':fmt(mp.mpf(5)*mp.log(2)/8*mp.sqrt(2/mp.pi)),
                     'alpha_optimal':fmt(2*mp.log(2)-3)}
    return {'status':'PASS', 'method':'Direct adjacent marked-weight and reference-mass recurrences, 80 digits by default.',
            'limitations':'Analytic tail formulas are evaluated numerically; mpmath roundoff is not interval-certified. Fixtures do not prove uniform or asymptotic statements.',
            'constants':constants, 'rare_parity':rare_parity(), 'exact_formula_CF_jacobians':jacobian_checks(),
            'rows':[numerical_case(n,digits) for n in ns]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,nargs='+')
    parser.add_argument('--extended',action='store_true',help='also run 10^10 and 10^10+1')
    parser.add_argument('--digits',type=int,default=80)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.n and args.extended:
        parser.error('choose --n or --extended')
    if args.output is not None:
        new_file_path(args.output)
    ns = args.n or DEFAULT_NS+((10000000000,10000000001) if args.extended else ())
    emit(run(ns,args.digits),args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
