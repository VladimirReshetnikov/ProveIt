"""Exact sign certificates for the fifth Stieltjes parameter derivatives.

All numerical enclosures use integer endpoints scaled by 10**80.
Only integer and Fraction arithmetic is used; no floating-point special
function is called. The analytic Euler--Maclaurin bound is documented in
n5_zero_transition.tex and in the baseline 09-zero-certificates.tex.

Usage: python certify_n5_zeros.py [output.json]
"""
from fractions import Fraction
from math import factorial, prod
import json
import sys
from pathlib import Path

SCALE = 10**80
TAYLOR_TERMS = 120
M = 24
RORDER = 16
INDEX = 5


def ceildiv(a, b):
    return -((-a)//b)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        self.lo = int(lo)
        self.hi = int(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def point(x):
        x = Fraction(x)
        return I((x.numerator*SCALE)//x.denominator,
                 ceildiv(x.numerator*SCALE, x.denominator))

    @staticmethod
    def rational_interval(lo, hi):
        return I(I.point(lo).lo, I.point(hi).hi)

    @staticmethod
    def cast(x):
        return x if isinstance(x, I) else I.point(x)

    def __add__(self, other):
        o = I.cast(other)
        return I(self.lo+o.lo, self.hi+o.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self+-I.cast(other)

    def __rsub__(self, other):
        return I.cast(other)+-self

    def __mul__(self, other):
        o = I.cast(other)
        v = [self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi]
        return I(min(v)//SCALE, ceildiv(max(v), SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return I(SCALE*SCALE//self.hi, ceildiv(SCALE*SCALE, self.lo))

    def __truediv__(self, other):
        return self*I.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return I.cast(other)*self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        if n == 0:
            return I.point(1)
        # For even powers crossing zero, use the known sign to avoid
        # dependency widening. This is a valid enclosure of the image.
        if n % 2 == 0:
            vals = [self.lo**n, self.hi**n]
            den = SCALE**(n-1)
            low = 0 if self.lo <= 0 <= self.hi else min(vals)//den
            return I(low, ceildiv(max(vals), den))
        den = SCALE**(n-1)
        return I(self.lo**n//den, ceildiv(self.hi**n, den))

    def sign(self):
        return 1 if self.lo > 0 else -1 if self.hi < 0 else 0

    def record(self):
        return {'lower_integer':str(self.lo), 'upper_integer':str(self.hi)}


def log_reduced(y):
    """Exact enclosure of log(y), for rational 1 <= y <= 2."""
    assert 1 <= y <= 2
    u = (y-1)/(y+1)
    ui = I.point(u)
    usq = ui*ui
    power = ui
    result = I.point(0)
    for j in range(TAYLOR_TERMS):
        result += 2*power/Fraction(2*j+1)
        power = power*usq
    remainder = 2*u**(2*TAYLOR_TERMS+1)/(
        (2*TAYLOR_TERMS+1)*(1-u*u))
    return I(result.lo, result.hi+I.point(remainder).hi)


LOG2 = log_reduced(Fraction(2))


def log_fraction(x):
    x = Fraction(x)
    assert x > 0
    y, j = x, 0
    while y < 1:
        y *= 2
        j -= 1
    while y >= 2:
        y /= 2
        j += 1
    return log_reduced(y)+j*LOG2


def log_interval(x):
    return I(log_fraction(Fraction(x.lo, SCALE)).lo,
             log_fraction(Fraction(x.hi, SCALE)).hi)


def elementary(k):
    e = [Fraction(1)]+[Fraction(0)]*INDEX
    for j in range(1, k+1):
        for r in range(min(j, INDEX), 0, -1):
            e[r] += e[r-1]/j
    return e


E = [elementary(k) for k in range(2*RORDER+5)]


def bernoulli_even(maximum):
    # The elementary triangular recurrence returns exact rational B_j;
    # its B_1 convention is irrelevant since only even j >= 2 are used.
    a = [Fraction(0)]*(maximum+1)
    out = {}
    for m in range(maximum+1):
        a[m] = Fraction(1, m+1)
        for j in range(m, 0, -1):
            a[j-1] = j*(a[j-1]-a[j])
        if m and m % 2 == 0:
            out[m] = a[0]
    return out


B = bernoulli_even(2*RORDER)
assert B[2] == Fraction(1, 6) and B[4] == Fraction(-1, 30)


def spectral_polynomial(k, v, n=INDEX):
    return sum((Fraction(factorial(n), factorial(n-i))*E[k][i]
                *(-v)**(n-i) for i in range(min(n, k)+1)),
               I.point(0))


def error_polynomial(L, v, n=INDEX):
    return sum((Fraction(factorial(n),
                         factorial(n-i-j)*L**j)*E[L][i]
                *v**(n-i-j)
                for i in range(min(n, L)+1)
                for j in range(n-i+1)), I.point(0))


def enclosure(k, lower_a, upper_a=None, n=INDEX):
    """Enclose V_{n,k}(a) on a rational interval, for 0 <= n <= 5."""
    assert 0 <= n <= INDEX
    if upper_a is None:
        upper_a = lower_a
    a = I.rational_interval(lower_a, upper_a)
    A = a+M
    assert A.lo > SCALE
    p = k+1
    v = log_interval(A)
    out = sum(((a/(a+m))**p*spectral_polynomial(k,log_interval(a+m),n)
               for m in range(M)), I.point(0))
    ratio = (a/A)**p
    out += ratio*(A/k*spectral_polynomial(k-1, v,n)
                  +spectral_polynomial(k, v,n)/2)
    for r in range(1, RORDER+1):
        factor = Fraction(B[2*r], factorial(2*r))*prod(
            range(k+1, k+2*r))
        out += ratio*factor/A**(2*r-1)*spectral_polynomial(k+2*r-1,v,n)
    L = k+2*RORDER
    err = ratio*Fraction(abs(B[2*RORDER]),factorial(2*RORDER))*prod(
        range(k+1,k+2*RORDER))/A**(2*RORDER-1)*error_polynomial(L,v,n)
    assert err.lo >= 0
    return I(out.lo-err.hi,out.hi+err.hi), err.hi


# These decimals are rational isolating endpoints, not assertions of
# computed exact roots. Every asserted sign is checked below.
BRACKETS = {
    1: [
        ('1.1378900542449414','1.1378900542449415'),
        ('1.6389372768448503','1.6389372768448504'),
        ('2.1249028498579805','2.1249028498579806')],
    2: [
        ('1.3713298168772550','1.3713298168772551'),
        ('1.9113619446041762','1.9113619446041763'),
        ('148.9122045692035618','148.9122045692035619')],
    3: [
        ('0.9409528529131887','0.9409528529131888'),
        ('1.1292935180347063','1.1292935180347064'),
        ('1.6357795548293846','1.6357795548293847'),
        ('6.1361342793896981','6.1361342793896982'),
        ('319.6184025568026870','319.6184025568026871')]
}
EXPECTED_PREVIOUS = {2:[-1,1,-1],3:[1,1,-1,1,-1]}


def decimal_outward(integer, places, upper):
    divisor = 10**(80-places)
    integer = ceildiv(integer,divisor) if upper else integer//divisor
    sign = '-' if integer < 0 else ''
    integer = abs(integer)
    return sign+str(integer//10**places)+'.'+str(integer%10**places).zfill(places)


def short_interval(x, places=12):
    return [decimal_outward(x.lo,places,False),
            decimal_outward(x.hi,places,True)]


def run():
    data = {
        'claim': 'gamma_5 has 3, 3, 5 positive simple derivative zeros at '
                 'orders 1, 2, 3, and exactly 5 at every order >= 3',
        'scale':str(SCALE),'stieltjes_index':INDEX,
        'log_series_terms':TAYLOR_TERMS,
        'euler_maclaurin_M':M,'euler_maclaurin_R':RORDER,
        'normalization':'V_(5,k)(a)=a^(k+1)*(-1)^(5+k)*gamma_5^(k)(a)/k!',
        'certificates':[]}
    for k in (3,2,1):
        for j,(lo,hi) in enumerate(BRACKETS[k]):
            left, le = enclosure(k,lo)
            right, re = enclosure(k,hi)
            want_left = (-1)**j
            assert left.sign() == want_left, (k,j,'left')
            assert right.sign() == -want_left, (k,j,'right')
            row = {'k':k,'j':j+1,'root_bracket':[lo,hi],
                   'left':left.record(),'right':right.record(),
                   'left_sign':left.sign(),'right_sign':right.sign(),
                   'left_error_upper_integer':str(le),
                   'right_error_upper_integer':str(re)}
            if k>1:
                previous, pe = enclosure(k-1,lo,hi)
                assert previous.sign() == EXPECTED_PREVIOUS[k][j], (k,j,'previous')
                row.update({'previous_order_interval':previous.record(),
                            'previous_order_sign':previous.sign(),
                            'previous_order_error_upper_integer':str(pe),
                            'previous_order_decimal_enclosure':short_interval(previous)})
            data['certificates'].append(row)
            print(k,j+1,lo,hi,
                  row.get('previous_order_decimal_enclosure',''),flush=True)
    data['n3_classical_endpoint_certificates'] = []
    for a, want in [('4/5',1),('11/10',-1),('3/2',1)]:
        val, error = enclosure(1,a,n=3)
        assert val.sign() == want, ('n3',a)
        data['n3_classical_endpoint_certificates'].append({
            'n':3,'k':1,'a':a,
            'normalization':'V_(3,1)(a)=a^2*gamma_3_prime(a)',
            'interval':val.record(),'sign':val.sign(),
            'decimal_enclosure':short_interval(val),
            'analytic_error_upper_integer':str(error)})
        print('n=3 k=1',a,short_interval(val),flush=True)
    data['all_assertions_passed'] = True
    target = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('n5_zero_certificates.json')
    target.write_text(json.dumps(data,indent=2)+'\n')
    print('Certified 22 fifth-index endpoint signs, 8 uniform critical-point '
          'signs, and 3 third-index endpoint signs.')
    print(target)


if __name__ == '__main__':
    run()
