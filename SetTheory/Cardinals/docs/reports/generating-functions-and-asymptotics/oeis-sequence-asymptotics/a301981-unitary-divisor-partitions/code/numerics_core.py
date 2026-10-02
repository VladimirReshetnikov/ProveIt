"""Reproducible unitary-partition arithmetic and asymptotic diagnostics.
Exact coefficient arithmetic and rational tail bounds are rigorous computations.
Floating roots, cumulants and ratios are NOT interval-certified.
"""
import math
from fractions import Fraction as F
from functools import lru_cache
import mpmath as mp


def weights(limit):
    b = [1] * (limit + 1)
    for p in range(2, limit + 1):
        if b[p] == 1:
            for k in range(p, limit + 1, p):
                v, pa = k, 1
                while v % p == 0:
                    v //= p
                    pa *= p
                b[k] *= pa + 1
    return b


def coefficients(limit, b, fermion):
    c = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for j in range(1, limit // d + 1):
            c[d * j] += d * b[d] * ((-1) ** (j + 1) if fermion else 1)
    a = [1] + [0] * limit
    for n in range(1, limit + 1):
        total = sum(c[k] * a[n-k] for k in range(1, n+1))
        assert total % n == 0
        a[n] = total // n
        assert a[n] > 0
    return a


def binomial_coefficients(limit, b, fermion):
    a = [1] + [0] * limit
    for k in range(1, limit + 1):
        out = a.copy()
        last = min(limit // k, b[k]) if fermion else limit // k
        for j in range(1, last + 1):
            c = math.comb(b[k], j) if fermion else math.comb(b[k]+j-1, j)
            for n in range(k*j, limit+1):
                out[n] += c * a[n-k*j]
        a = out
    return a


def hermites(z, degree):
    h = [mp.mpf(1)]
    if degree:
        h.append(z)
    for d in range(1, degree):
        h.append(z*h[-1] - d*h[-2])
    return h


def multiplicities(grade, r=3):
    if grade == 0:
        yield {}
        return
    if r-2 > grade:
        return
    for m in range(grade // (r-2) + 1):
        rest = grade - m*(r-2)
        if rest == 0:
            yield {r: m} if m else {}
        else:
            for others in multiplicities(rest, r+1):
                yield dict(others) | ({r: m} if m else {})


def grades(lam, delta, maximum):
    h = hermites(delta, 3*maximum)
    out = [mp.mpf(1)]
    for j in range(1, maximum+1):
        value = mp.mpf(0)
        for powers in multiplicities(j):
            degree = sum(r*m for r, m in powers.items())
            term = h[degree]
            for r, m in powers.items():
                term *= (lam[r]/math.factorial(r))**m/math.factorial(m)
            value += term
        out.append(value)
    return out


class Model:
    def __init__(self, fermion, cutoff=1000, maximum_derivative=7):
        self.fermion = fermion
        self.eps = -1 if fermion else 1
        self.cutoff = cutoff
        self.maximum_derivative = maximum_derivative
        self.b = weights(cutoff)
        self.A = mp.pi**2/(8 if fermion else 6)
        self.polynomials = [[0, 1]]
        for r in range(1, maximum_derivative):
            p = self.polynomials[-1]
            q = [0] * (len(p)+1)
            for j in range(1, len(p)):
                q[j] += j*p[j]
                q[j+1] += self.eps*(r-j)*p[j]
            self.polynomials.append(q)

    def vals(self, t, rmax=None):
        if rmax is None:
            rmax = self.maximum_derivative
        out = [mp.mpf(0)] * (rmax+1)
        for k in range(1, self.cutoff+1):
            q = mp.exp(-k*t)
            out[0] += self.b[k]*(mp.log1p(q) if self.fermion else -mp.log1p(-q))
            for r in range(1, rmax+1):
                p = mp.polyval(self.polynomials[r-1][::-1], q)
                out[r] += self.b[k]*k**r*p/(1-self.eps*q)**r
        return out

    def centered_terms(self, values):
        f, k1, v, k3, k4, k5, k6 = values[:7]
        c1 = k4/(8*v**2)-5*k3**2/(24*v**3)
        c2 = (-k6/(48*v**3)+7*k3*k5/(48*v**4)
              +35*k4**2/(384*v**4)-35*k3**2*k4/(64*v**5)
              +385*k3**4/(1152*v**6))
        return c1, c2

    def centered_logmodel(self, t, order):
        values = self.vals(t, 6)
        f, k1, v = values[:3]
        c1, c2 = self.centered_terms(values)
        correction = 1 + (c1 if order >= 1 else 0) + (c2 if order >= 2 else 0)
        return f+t*k1-mp.log(2*mp.pi*v)/2+mp.log(correction), k1

    @lru_cache(maxsize=256)
    def _data(self, x, precision):
        assert precision == mp.mp.dps
        t = (2*self.A/x)**(mp.mpf(1)/3)
        values = self.vals(t, 7)
        v = values[2]
        delta = (x-values[1])/mp.sqrt(v)
        lam = {r: values[r]/v**(mp.mpf(r)/2) for r in range(3, 8)}
        q = grades(lam, delta, 5)
        return t, values, delta, lam, q

    def data(self, x):
        return self._data(mp.mpf(x), mp.mp.dps)

    def explicit_logmodel(self, x, order):
        t, values, delta, lam, q = self.data(x)
        return (values[0]+x*t-mp.log(2*mp.pi*values[2])/2
                -delta**2/2+mp.log(sum(q[:2*order+2])))


def unitary_diagnostics():
    mp.mp.dps = 50
    limit = 1000
    b = weights(limit)
    for k in range(1, 101):
        assert b[k] == sum(d for d in range(1, k+1)
                           if k % d == 0 and math.gcd(d, k//d) == 1)
    out = {}
    for fermion in (True, False):
        a = coefficients(limit, b, fermion)
        if fermion:
            assert a[:16] == [1,1,3,7,12,26,52,92,170,310,541,945,1636,2760,4639,7743]
        A = mp.pi**2/(8 if fermion else 6)
        C = 3*(A/4)**(mp.mpf(1)/3)
        K = (1/(2**(mp.mpf(4)/3)*mp.sqrt(3)*mp.pi**(mp.mpf(1)/6))
             if fermion else mp.glaisher**6*mp.exp(-mp.mpf(1)/2)
             /(2*3**(mp.mpf(5)/6)*mp.pi**(mp.mpf(1)/3)))
        power = mp.mpf(2)/3 if fermion else mp.mpf(5)/6
        rows = []
        for n in (20,50,100,200,500,1000):
            approximation = K*n**(-power)*mp.exp(C*n**(mp.mpf(2)/3))
            rows.append({'n':n, 'exact_over_OEIS_model':mp.nstr(mp.mpf(a[n])/approximation,25)})
        out['A301982' if fermion else 'A301981'] = {'first_terms':a[:20], 'ratios':rows}
    for fermion in (True,False):
        def kernel(s):
            value = mp.gamma(s)*mp.zeta(s+1)*mp.zeta(s)*mp.zeta(s-1)/mp.zeta(2*s-1)
            return value*(1-2**(-s) if fermion else 1)
        residue = mp.limit(lambda s:(s-2)*kernel(s),2)
        expected = mp.pi**2/(8 if fermion else 6)
        assert abs(residue-expected)<mp.mpf('1e-40')
        out['residue_2_'+str(fermion)] = mp.nstr(residue,35)
    return out


def saddle_diagnostics(cutoff=1000, precision=60, include_fixed=False):
    mp.mp.dps = precision
    rows = []
    for fermion in (True,False):
        model = Model(fermion, cutoff, 6)
        a = coefficients(1000, model.b, fermion)
        for n in (50,100,200,500,1000):
            t = (2*model.A/n)**(mp.mpf(1)/3)
            for _ in range(8):
                values = model.vals(t,2)
                change = (values[1]-n)/values[2]
                t += change
                if abs(change) < mp.mpf('1e-50'):
                    break
            values = model.vals(t,6)
            f,k1,v,k3,k4,k5,k6 = values
            c1,c2 = model.centered_terms(values)
            leading = mp.exp(f+n*t)/mp.sqrt(2*mp.pi*v)
            errors = [mp.mpf(a[n])/leading-1,
                      mp.mpf(a[n])/(leading*(1+c1))-1,
                      mp.mpf(a[n])/(leading*(1+c1+c2))-1]
            row = {'sequence':'A301982' if fermion else 'A301981', 'n':n,
                   't':mp.nstr(t,22),'saddle_error':mp.nstr(k1-n,5),
                   'C1':mp.nstr(c1,20),'C2':mp.nstr(c2,20),
                   'relative_errors_M0_M1_M2':[mp.nstr(e,20) for e in errors],
                   'scaled_errors_t2_t4_t6':[mp.nstr(e/t**(2*(j+1)),20) for j,e in enumerate(errors)]}
            if include_fixed:
                t0 = (2*model.A/n)**(mp.mpf(1)/3)
                f0 = model.vals(t0,0)[0]
                fixed = mp.exp(f0+n*t0)*t0**2/mp.sqrt(12*mp.pi*model.A)
                row.update({'fixed_saddle_relative_error':mp.nstr(mp.mpf(a[n])/fixed-1,20),
                            'location_difference_over_t0_squared':mp.nstr((t-t0)/t0**2,20),
                            'stationary_exponent_difference':mp.nstr(f0+n*t0-f-n*t,20)})
            rows.append(row)
    return rows


def rational_tail_bounds(cutoffs, largest_r):
    # Exact Taylor bounds establish 2.7 < e < 2.72.
    assert sum(F(1,math.factorial(k)) for k in range(6)) > F(27,10)
    upper = sum(F(1,math.factorial(k)) for k in range(8))+F(1,math.factorial(8))*F(9,8)
    assert upper < F(68,25)
    ceilings = (3,8,21,55,149)
    assert all(F(68,25)**j < v for j,v in enumerate(ceilings,1))
    lower = sum(F(sum(k*k for k in range(10*(j-1)+1,10*j+1)),1+v)
                for j,v in enumerate(ceilings,1))
    assert lower > 1000
    bounds=[]
    for cutoff in cutoffs:
        assert cutoff % 10 == 0
        for r in range(largest_r+1):
            power = r+2
            constant = F(27,17) if r == 0 else math.factorial(r-1)*F(27,17)**r
            bound = constant*F(10,27)**(cutoff//10)*sum(
                math.comb(power,i)*(cutoff+1)**(power-i)*math.factorial(i)*10**(i+1)
                for i in range(power+1))
            bounds.append({'cutoff':cutoff,'derivative_order':r,
                           'bound_numerator':str(bound.numerator),
                           'bound_denominator':str(bound.denominator),
                           'approximate_decimal_for_readability':format(float(bound),'.8e')})
    return lower,bounds


def offcenter_diagnostics(cutoff=1200, precision=70):
    mp.mp.dps=precision
    limit=500
    result={'cutoff':cutoff,'precision':precision,
            'exact_binomial_vs_recurrence_coefficients_checked_per_sequence':limit+1,
            'cases':[], 'Fourier_sign_checks':[]}
    delta=mp.mpf('0.4')
    h=hermites(delta,7)
    for degree in range(8):
        z=2*mp.quad(lambda x:mp.re(mp.exp(-x*x/2-1j*delta*x)*(1j*x)**degree),
                    [0,mp.inf])/mp.sqrt(2*mp.pi)
        rhs=h[degree]*mp.exp(-delta*delta/2)
        assert abs(z-rhs)<mp.mpf('1e-55')
        result['Fourier_sign_checks'].append({'degree':degree,'absolute_error':mp.nstr(abs(z-rhs),5)})
    for fermion in (True,False):
        model=Model(fermion,cutoff,7)
        a=binomial_coefficients(limit,model.b,fermion)
        assert a==coefficients(limit,model.b,fermion)
        for n in (30,100,300,500):
            t,values,delta,lam,q=model.data(n)
            assert abs(delta)<1
            h=hermites(delta,9)
            assert mp.almosteq(q[1],lam[3]*h[3]/6)
            assert mp.almosteq(q[2],lam[4]*h[4]/24+lam[3]**2*h[6]/72)
            qzero=grades(lam,mp.mpf(0),5)
            assert all(qzero[j]==0 for j in (1,3,5))
            assert mp.almosteq(qzero[2],lam[4]/8-5*lam[3]**2/24)
            leading=mp.exp(values[0]+n*t-delta**2/2)/mp.sqrt(2*mp.pi*values[2])
            errors=[]
            for order in range(3):
                approximation=leading*sum(q[:2*order+2])
                error=mp.mpf(a[n])/approximation-1
                even_only=leading*sum(q[j] for j in range(2*order+2) if j%2==0)
                errors.append({'M':order,'relative_error':mp.nstr(error,25),
                               'scaled_by_t_2Mplus2':mp.nstr(error/t**(2*order+2),22),
                               'error_if_odd_grades_incorrectly_deleted':mp.nstr(mp.mpf(a[n])/even_only-1,25)})
            result['cases'].append({'sequence':'A301982' if fermion else 'A301981','n':n,
                                    't0':mp.nstr(t,25),'delta':mp.nstr(delta,25),
                                    'grades_1_through_5':[mp.nstr(x,25) for x in q[1:]],'errors':errors})
    return result


def inverse_diagnostics(explicit=False):
    mp.mp.dps=70
    rows=[]
    for fermion in (True,False):
        cutoff=1200 if explicit else 1500
        model=Model(fermion,cutoff,7)
        a=coefficients(1001 if not explicit else 500,model.b,fermion)
        indices=(100,300) if explicit else (50,200,1000)
        for n in indices:
            targets=(['coefficient'] if explicit and n==100 else ['coefficient','midpoint'])
            for target in targets:
                logy=mp.log(a[n]) if target=='coefficient' else (mp.log(a[n])+mp.log(a[n+1]))/2
                estimates=[]
                for order in range(3):
                    if explicit:
                        x=mp.findroot(lambda x:model.explicit_logmodel(x,order)-logy,
                                      (mp.mpf(n),mp.mpf(n)+1),tol=mp.mpf('1e-55'))
                        t=(2*model.A/x)**(mp.mpf(1)/3)
                        residual=model.explicit_logmodel(x,order)-logy
                    else:
                        t0=(2*model.A/n)**(mp.mpf(1)/3)
                        t=mp.findroot(lambda t:model.centered_logmodel(t,order)[0]-logy,
                                      (t0,t0*mp.mpf('1.001')),tol=mp.mpf('1e-60'))
                        value,x=model.centered_logmodel(t,order)
                        residual=value-logy
                    difference=x-n
                    if target=='midpoint':assert int(mp.ceil(x))==n+1
                    estimates.append({'M':order,'continuous_inverse':mp.nstr(x,30),
                                      'difference_from_n':mp.nstr(difference,25),
                                      'difference_scaled_by_t_power':mp.nstr(difference/t**(2*order+1),22)
                                         if target=='coefficient' else None,
                                      'rounded_inverse':int(mp.ceil(x)),
                                      'log_equation_residual':mp.nstr(residual,5)})
                rows.append({'sequence':'A301982' if fermion else 'A301981','n':n,'target':target,
                             'true_threshold':n if target=='coefficient' else n+1,'estimates':estimates})
    return rows
