#!/usr/bin/env python3
"""Exact finite-order coefficient checks for Report198 / OEIS A373273.

All arithmetic uses fractions.Fraction.  The calculations check algebraic
identities, Gaussian moments, and radial integrals after their stated analytic
reductions.  They do not certify analytic error bounds, asymptotic onset,
minor-arc localization, or any higher-order expansion.  No floating-point
comparison, numerical tolerance, or assert statement is used.

run() returns a deterministic, JSON-serializable object.  Executing this file
prints that object and returns a nonzero exit status if any identity fails.
"""

from fractions import Fraction as F
import json
import sys


class Poly:
    """Sparse Laurent polynomials over Q in independent formal symbols."""

    def __init__(self, terms=None):
        self.terms = {}
        for monomial, coefficient in (terms or {}).items():
            coefficient = F(coefficient)
            powers = dict(monomial)
            key = tuple(sorted((name, power) for name, power in powers.items() if power))
            self.terms[key] = self.terms.get(key, F(0)) + coefficient
        self.terms = {key: coefficient for key, coefficient in self.terms.items() if coefficient}

    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly({(): F(value)})

    def __add__(self, other):
        terms = dict(self.terms)
        for key, value in Poly.lift(other).terms.items():
            terms[key] = terms.get(key, F(0)) + value
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly.lift(other))

    def __rsub__(self, other):
        return Poly.lift(other) - self

    def __mul__(self, other):
        result = {}
        for left, a in self.terms.items():
            for right, b in Poly.lift(other).terms.items():
                powers = dict(left)
                for name, power in right:
                    powers[name] = powers.get(name, 0) + power
                key = tuple(sorted(powers.items()))
                result[key] = result.get(key, F(0)) + a * b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError("Only integer powers are supported")
        if exponent < 0:
            if len(self.terms) != 1:
                raise ValueError("Negative powers require a nonzero monomial")
            (monomial, coefficient), = self.terms.items()
            return Poly({tuple((name, power * exponent) for name, power in monomial):
                         coefficient ** exponent})
        result = Poly.lift(1)
        factor = self
        while exponent:
            if exponent % 2:
                result = result * factor
            factor = factor * factor
            exponent //= 2
        return result

    def __truediv__(self, other):
        return self * (Poly.lift(other) ** -1)

    def __rtruediv__(self, other):
        return Poly.lift(other) / self

    def __eq__(self, other):
        return self.terms == Poly.lift(other).terms

    def coefficient(self, symbol, exponent):
        return Poly({tuple((name, power) for name, power in monomial if name != symbol): value
                     for monomial, value in self.terms.items()
                     if dict(monomial).get(symbol, 0) == exponent})

    def truncate(self, symbol, maximum):
        return Poly({monomial: value for monomial, value in self.terms.items()
                     if dict(monomial).get(symbol, 0) <= maximum})

    def substitute(self, symbol, replacement):
        result = Poly.lift(0)
        replacement = Poly.lift(replacement)
        for monomial, value in self.terms.items():
            powers = dict(monomial)
            exponent = powers.pop(symbol, 0)
            result += Poly({tuple(powers.items()): value}) * replacement ** exponent
        return result

    def derivative(self, symbol):
        result=Poly.lift(0)
        for monomial, coefficient in self.terms.items():
            powers=dict(monomial); exponent=powers.get(symbol,0)
            if exponent:
                powers[symbol]=exponent-1
                result += Poly({tuple(powers.items()):coefficient*exponent})
        return result

    def text(self):
        if not self.terms:
            return "0"
        pieces = []
        for monomial, coefficient in sorted(self.terms.items()):
            factors = [str(coefficient)]
            factors += [name if power == 1 else name + "^" + str(power)
                        for name, power in monomial]
            pieces.append("*".join(factors))
        return " + ".join(pieces).replace(" + -", " - ")


def symbol(name):
    return Poly({((name, 1),): F(1)})


def geometric_inverse(z, order):
    """Finite Taylor polynomial of 1/(1+z); no remainder claim is made."""
    z = Poly.lift(z)
    return sum(((-z) ** j for j in range(order + 1)), Poly.lift(0))


def exponential(z, order):
    """Finite Taylor polynomial of exp(z)."""
    result = Poly.lift(1)
    term = Poly.lift(1)
    for j in range(1, order + 1):
        term = term * z / j
        result += term
    return result


def log_one_plus(z, order):
    return sum((F((-1) ** (j + 1), j) * z ** j for j in range(1, order + 1)),
               Poly.lift(0))


def binomial_one_plus(z, power, order):
    coefficient = F(1)
    result = Poly.lift(1)
    for j in range(1, order + 1):
        coefficient *= (F(power) - j + 1) / j
        result += coefficient * z ** j
    return result


def radial_integral(k):
    """Exact value of integral_0^infinity x^-k exp(-1/x^2) dx, k > 1.

    Uses I_2=sqrt(pi)/2, I_3=1/2 and I_(k+2)=(k-1) I_k/2,
    which follow from the gamma-integral substitution and integration by parts.
    """
    if not isinstance(k, int) or k < 2:
        raise ValueError("The integral requires an integer k >= 2")
    if k % 2 == 0:
        value = symbol("sqrt_pi") / 2
        first = 2
    else:
        value = Poly.lift(F(1, 2))
        first = 3
    for current in range(first, k, 2):
        value *= F(current - 1, 2)
    return value


def integrate_radial_profile(profile, coordinate):
    """Integrate a Laurent profile multiplied by exp(-1/coordinate**2)."""
    result = Poly.lift(0)
    for monomial, coefficient in profile.terms.items():
        powers = dict(monomial)
        exponent = powers.pop(coordinate, 0)
        result += Poly({tuple(powers.items()): coefficient}) * radial_integral(-exponent)
    return result


def gaussian_moment(degree):
    """Moment under exp(-v**2)/sqrt(pi), evaluated by exact recurrence."""
    if not isinstance(degree, int) or degree < 0:
        raise ValueError("The moment degree must be a nonnegative integer")
    if degree % 2:
        return F(0)
    result = F(1)
    for j in range(2, degree + 1, 2):
        result *= F(j - 1, 2)
    return result


def run():
    checks=[]
    def check(name, obtained, expected):
        obtained,expected=Poly.lift(obtained),Poly.lift(expected)
        residual=obtained-expected
        checks.append({'name':name,'passed':residual==0,
                       'obtained':obtained.text(),'expected':expected.text(),
                       'residual':residual.text()})
    h,x,y,m=(symbol(s) for s in ('h','x','y','m'))
    sp=symbol('sqrt_pi')
    check('radial_I2',radial_integral(2),sp/2)
    check('radial_I3',radial_integral(3),F(1,2))
    check('radial_I5',radial_integral(5),F(1,2))
    s2num=(m+1)*(2*m+1)-4*m*(m+1)+m*(2*m+1)
    check('S2_cleared_denominator',s2num,1)
    s3num=Poly.lift(0)
    for omitted,weight in enumerate((1,-3,3,-1)):
        term=Poly.lift(weight)
        for j in range(4):
            if j!=omitted:term*=3*m+j
        s3num+=term
    check('S3_cleared_denominator',s3num,6)
    anc=(x**-2*geometric_inverse(h/x,2)).truncate('h',2)
    ac=(y**-2*geometric_inverse(-h**2/(4*y**2),2)).truncate('h',2)
    enc=exponential(-(anc-x**-2),2).truncate('h',2)
    ec=exponential(-(ac-y**-2),2).truncate('h',2)
    check('A_noncentered',anc,x**-2-h*x**-3+h**2*x**-4)
    check('A_centered',ac,y**-2+h**2/(4*y**4))
    tnc=(h/(4*x**3)*geometric_inverse(h/x,2)*geometric_inverse(h/(2*x),2)).truncate('h',2)
    tc=(h/(4*y**3)*geometric_inverse(-h**2/(4*y**2),2)).truncate('h',2)
    weighted_nc=(x/h*tnc*enc/2).truncate('h',1)
    weighted_c=((y/h-F(1,2))*tc*ec/2).truncate('h',1)
    check('H2_noncentered_leading_profile',weighted_nc.coefficient('h',0),1/(8*x**2))
    check('H2_noncentered_next_profile',weighted_nc.coefficient('h',1),1/(8*x**5)-3/(16*x**3))
    check('H2_centered_next_profile',weighted_c.coefficient('h',1),-1/(16*y**3))
    for name,profile,coordinate in (('noncentered',weighted_nc,'x'),('centered',weighted_c,'y')):
        check('H2_'+name+'_leading_integral',integrate_radial_profile(profile.coefficient('h',0),coordinate),sp/16)
        check('H2_'+name+'_local_constant',integrate_radial_profile(profile.coefficient('h',1),coordinate),F(-1,32))
    # The far-tail integral value is the analytic reduction in the manuscript;
    # this exact check verifies the change-of-variable and endpoint arithmetic.
    far_tail=F(1,8)*F(-1,2)
    check('H2_far_tail_endpoint_arithmetic',far_tail,F(-1,16))
    check('H2_total_constant',F(-1,32)+far_tail,F(-3,32))
    check('H3_constant',F(2,81)*radial_integral(3),F(1,81))
    check('H22_constant',-radial_integral(5)/128,F(-1,256))
    check('Z_zero_removable_contribution',F(-1,12)+F(1,4),F(1,6))
    check('square_root_coefficient',-sp/2+sp/16,-7*sp/16)
    gamma,zeta=(symbol(s) for s in ('gamma','zeta_prime_minus_one'))
    d=F(1,24)-gamma/8-zeta
    e=F(13,144)+zeta+gamma/12
    check('D_plus_E',d+e,F(19,144)-gamma/24)
    rational=F(1,4)+F(1,6)+F(19,144)-F(3,32)+F(1,81)-F(1,256)
    check('rational_constant_K',rational,F(9607,20736))
    check('full_sector_constant_K',F(1,4)+F(1,6)+d+e-F(3,32)+F(1,81)-F(1,256),F(9607,20736)-gamma/24)
    beta,s=(symbol(k) for k in ('beta','s'))
    m2,m4,m6=(gaussian_moment(k) for k in (2,4,6))
    check('Gaussian_moment_2',m2,F(1,2))
    check('Gaussian_moment_4',m4,F(3,4))
    check('Gaussian_moment_6',m6,F(15,8))
    saddle=m4-m6/2-beta*m4-beta*(beta-1)*m2/2
    absolute=saddle.substitute('beta',s+F(1,2))
    ratio=absolute-absolute.substitute('s',0)
    check('absolute_saddle_polynomial_times_A',absolute,-(s+1)*(s+2)/4)
    check('partition_saddle_coefficient_times_A',absolute.substitute('s',0),F(-1,2))
    check('normalized_saddle_polynomial_times_A',ratio,-s*(s+3)/4)
    check('normalized_saddle_at_minus_one',ratio.substitute('s',-1),F(1,2))
    check('normalized_saddle_at_minus_half',ratio.substitute('s',F(-1,2)),F(5,16))
    check('normalized_saddle_at_zero',ratio.substitute('s',0),0)
    check('log_amplitude_derivative_constant',-ratio.derivative('s').substitute('s',-1),F(1,4))
    ell,A=(symbol(k) for k in ('ell','A'))
    c=F(3,2)-gamma/2
    K=F(9607,20736)-gamma/24
    canonical_constant=K+(c/2+F(1,8))/A
    check('canonical_constant',canonical_constant,K+(F(7,8)-gamma/4)/A)
    canonical_order_zero=(F(1,24)+1/(4*A))*ell+canonical_constant
    absolute_order_zero=canonical_order_zero-(ell/2+c)/(2*A)
    check('absolute_order_zero_cancellation',absolute_order_zero,ell/24+K+1/(8*A))
    failures=[row['name'] for row in checks if not row['passed']]
    if failures:raise ValueError('exact symbolic failures: '+', '.join(failures))
    return {'schema':'report198-symbolic-v1','report':198,'sequence':'A373273',
            'status':'PASS','arithmetic':'fractions.Fraction; sparse Laurent polynomials',
            'check_count':len(checks),'all_passed':True,
            'scope':'Exact finite algebra after stated analytic reductions only; no integral convergence, sector error, effective onset or inverse-ceiling certificate',
            'checks':checks}


if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
