#!/usr/bin/env python3
"""Fixed, exact bounded diagnostics for Report284; universal proofs are in article.tex."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from itertools import product, combinations
from math import comb, factorial, gcd, prod
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).absolute().parents[1]


def require(value, message):
    if not value:
        raise RuntimeError(message)


def bounded(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' outside its exact bounded domain')
    return value


def parameters(d):
    bounded(d, 1, 30, 'd')
    M = 2 ** (d + 2) + 1
    return M, (6 ** d - 1) // 5, Q(1, 20 * 6 ** (d - 1) * M)


def classical_parameters(k):
    bounded(k, 2, 20, 'k')
    R = (k - 2) * (k - 1) // 2
    A = (2 ** k + 1) * 6 ** R
    return A, Q(3, 10 * A), 2 * A + 1


def partial_extensions(n, m, data):
    bounded(n, 1, 6, 'n'); bounded(m, 2, 3, 'm')
    if (type(data) is not dict or any(type(x) is not int or not 0 <= x < n
            or type(y) is not int or not 0 <= y < m for x, y in data.items())):
        raise ValueError('invalid partial map')
    if 4 * len(data) <= 3 * n:
        raise ValueError('domain must have density strictly greater than 3/4')
    if any((x+y) % n in data and data[(x+y) % n] != (data[x]+data[y]) % m
           for x in data for y in data):
        return None
    return tuple(c for c in range(m) if n*c % m == 0
                 and all(data[x] == c*x % m for x in data))


def phase_difference(values, a, modulus):
    n = len(values)
    return tuple((values[x] - values[(x-a) % n]) % modulus for x in range(n))


# Exact cyclotomic rings Q[z]/Phi_n(z), for these small fixed conductors.
# Phi_p=1+x+...+x^(p-1) for primes, and Phi_4=x^2+1.
PHI = {2: (1, 1), 3: (1, 1, 1), 4: (1, 0, 1),
       5: (1, 1, 1, 1, 1), 7: (1, 1, 1, 1, 1, 1, 1)}


class Cyclo:
    """Exact bounded cyclotomic arithmetic, no floating conversions or tolerances."""
    __slots__ = ('n', 'a')

    def __init__(self, n, coefficients=()):
        if type(n) is not int or n not in PHI:
            raise ValueError('supported conductors are 2, 3, 4, 5, 7')
        if (type(coefficients) not in (tuple, list) or len(coefficients) > 64
                or any(type(c) not in (int, Q) for c in coefficients)):
            raise ValueError('bounded exact coefficient sequence required')
        if any(abs(c.numerator if type(c) is Q else c).bit_length() > 4096
               or (type(c) is Q and c.denominator.bit_length() > 4096) for c in coefficients):
            raise ValueError('coefficient bit budget exceeded')
        p = PHI[n]; degree = len(p) - 1
        a = [Q(c) for c in coefficients]
        for j in range(len(a)-1, degree-1, -1):
            v = a[j]
            for i in range(degree):
                a[j-degree+i] -= v*p[i]
        a = a[:degree] + [Q(0)] * max(0, degree-len(a))
        self.n = n; self.a = tuple(a)

    def coerce(self, other):
        if type(other) in (int, Q):
            return Cyclo(self.n, (other,))
        if type(other) is not Cyclo or other.n != self.n:
            raise ValueError('same conductor and exact scalar required')
        return other

    def __add__(self, other):
        other = self.coerce(other)
        return Cyclo(self.n, tuple(a+b for a,b in zip(self.a, other.a)))

    __radd__ = __add__

    def __neg__(self):
        return Cyclo(self.n, tuple(-a for a in self.a))

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __mul__(self, other):
        other = self.coerce(other)
        a = [Q(0)] * (2*len(self.a)-1)
        for i, x in enumerate(self.a):
            for j, y in enumerate(other.a):
                a[i+j] += x*y
        return Cyclo(self.n, a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if type(other) not in (int, Q) or other == 0:
            raise ValueError('nonzero exact scalar required')
        return Cyclo(self.n, tuple(a/other for a in self.a))

    def __eq__(self, other):
        if type(other) in (int, Q):
            other = Cyclo(self.n, (other,))
        return type(other) is Cyclo and self.n == other.n and self.a == other.a

    def conjugate(self):
        return sum((c*root(self.n, -j) for j, c in enumerate(self.a)), Cyclo(self.n))

    def norm_square(self):
        return self*self.conjugate()

    def serialized(self):
        return [str(a) for a in self.a]


def root(n, exponent):
    if type(n) is not int or n not in PHI or type(exponent) is not int:
        raise ValueError('supported conductor and integral exponent required')
    bounded(exponent, -1000000, 1000000, 'exponent')
    return Cyclo(n, tuple([0]*(exponent % n) + [1]))


def difference(f, a):
    n = len(f)
    return tuple(f[x] * f[(x-a) % n].conjugate() for x in range(n))


def iterated(f, inc):
    for a in inc:
        f = difference(f, a)
    return f


def mean(f):
    return sum(f, Cyclo(f[0].n))/len(f)


def fourier(f):
    n = len(f)
    return tuple(sum((f[x]*root(n, -r*x) for x in range(n)), Cyclo(n))/n
                 for r in range(n))


def q_squared(f, k):
    n = len(f)
    return sum((mean(iterated(f, inc)).norm_square()
                for inc in product(range(n), repeat=k-1)), Cyclo(n))/n**(k-1)


def q_cube(f, k):
    n = len(f); total = Cyclo(n)
    vertices = tuple(product((0,1), repeat=k))
    for inc in product(range(n), repeat=k):
        for x in range(n):
            z = Cyclo(n, (1,))
            for omega in vertices:
                y = (x-sum(a*b for a,b in zip(inc, omega))) % n
                z = z*(f[y].conjugate() if sum(omega) % 2 else f[y])
            total = total+z
    return total/n**(k+1)


def check_constants():
    rows = []; previous = 0
    for d in range(1,31):
        M, C, eps = parameters(d)
        require(C == 1+6*previous, 'extension recurrence'); previous = C
        density = 1-(6**d-1)*M*eps
        require(density == Q(7,10)+Q(1,20*6**(d-1)), 'endpoint density')
        require(6**(d-1)*5*M*eps == Q(1,4), 'induction endpoint')
        require(2**d*eps < Q(1,80), 'polar coefficient loss')
        require((Q(3,4)+2**d*eps)**2 < Q(4,5), 'coefficient target')
        sym = Q(1,2**(d+1)*(6**d-1)*M)
        require(sym <= eps and (6**d-1)*M*sym == Q(1,2**(d+1)), 'symmetry endpoint')
        rows.append(dict(d=d, M=M, C=C, epsilon_max=str(eps),
                         density_lower_expression=str(density), epsilon_sym=str(sym)))
    require(Q(4,5)-Q(64,81) == Q(4,405) > 0, 'character rigidity margin')
    require(2*Q(3,4)**2 == Q(9,8) > 1, 'two Fourier witnesses')
    require(Q(7,10)*Q(9,16) == Q(63,160), 'coarse energy')
    return rows


def check_dense_maps():
    kernels = 0; tested = 0; valid = 0
    for n in range(2,41):
        for c in range(1,n):
            require(2*sum(c*x % n == 0 for x in range(n)) <= n, 'kernel support')
            kernels += 1
    for n in range(1,7):
        for m in (2,3):
            for size in range(n+1):
                if 4*size <= 3*n:
                    continue
                for domain in combinations(range(n),size):
                    for values in product(range(m), repeat=size):
                        tested += 1
                        answer = partial_extensions(n,m,dict(zip(domain,values)))
                        if answer is not None:
                            valid += 1
                            require(len(answer) == 1, 'dense extension uniqueness')
    return dict(nonzero_kernel_cases=kernels, candidate_partial_maps=tested,
                partially_additive_maps=valid)


def check_support():
    families = []; total = 0
    for dims in ((1,), (2,), (1,1), (2,1), (2,2), (1,1,1),
                 (2,1,1), (2,2,2), (1,1,1,1), (2,1,1,1)):
        d = len(dims)
        entries = list(product(*(range(m) for m in dims)))
        points = list(product(*(range(2**m) for m in dims)))
        minimum = len(points)
        for coeffs in product((0,1),repeat=len(entries)):
            if not any(coeffs):
                continue
            support = 0
            for x in points:
                value = 0
                for c, entry in zip(coeffs,entries):
                    term = c
                    for xi, bit in zip(x,entry):
                        term *= (xi >> bit) & 1
                    value ^= term
                support += value
            require(support*2**d >= len(points), 'nonzero multilinear support')
            minimum = min(minimum,support); total += 1
        require(minimum*2**d == len(points), 'sharp support family')
        families.append(dict(factor_dimensions=dims, minimum_support=minimum,
                             domain_size=len(points), maps=2**len(entries)-1))
    # Generic partial data at equality: this is not a Fourier counterexample.
    for d in range(1,9):
        points = list(product(range(4),*(range(2) for _ in range(d-1))))
        A = {x:(x[0]&1)*int(all(y == 1 for y in x[1:])) for x in points}
        support = [x for x in points if A[x]]
        phi = {x:int(x == support[0]) for x in points}
        require(len(support) == 2, 'equality example support')
        require(Q(sum(phi[x] != 0 for x in points),len(points)) == Q(1,2**(d+1)), 'first equality witness')
        require(Q(sum(phi[x] != A[x] for x in points),len(points)) == Q(1,2**(d+1)), 'second equality witness')
    return dict(nonzero_maps=total, families=families, generic_equality_examples=8)


def check_torsion():
    counts = []
    for d in range(1,9):
        f = (Q(0), Q(1,2**(d+1)))
        for inc in product(range(2), repeat=d):
            h = f
            for a in inc:
                h = phase_difference(h,a,1)
            expected = (Q(3,4),Q(1,4)) if all(inc) else (Q(0),Q(0))
            require(h == expected, 'torsion derivative')
            require((h[1]-h[0]) % 1 == Q(int(all(inc)),2), 'torsion frequency sign')
        for inc in product(range(2), repeat=d+2):
            h = f
            for a in inc:
                h = phase_difference(h,a,1)
            require(h == (0,0), 'torsion exact extremizer')
        require(f[1] not in (0,Q(1,2)), 'torsion classical obstruction')
        counts.append(dict(d=d, derivative_tuples=2**d, top_order_tuples=2**(d+2)))
    return counts


def check_descent():
    rows = []
    for k in range(2,21):
        A, eps, linear = classical_parameters(k)
        delta = A*eps; r = k-2
        require(delta == Q(3,10), 'terminal defect')
        require((2**k+1)*eps*6**(r*(r+1)//2) == delta, 'single polar loss')
        stages = []
        for d in range(r,0,-1):
            t = delta/6**(d*(d+1)//2)
            require(t <= Q(1,20*6**(d-1)), 'stage admissibility')
            require(6**d*t == delta/6**((d-1)*d//2), 'stage recurrence')
            require(20*6**(d-1)*t == Q(1,6**(d*(d-1)//2)), 'stage exact endpoint')
            stages.append(dict(d=d,tau=str(t)))
        rows.append(dict(k=k,A=A,epsilon_max=str(eps),squared_error_constant=linear,stages=stages))
    return rows


def check_polynomial():
    rows = []
    for n,d in ((3,1),(5,1),(5,2),(5,3),(7,1),(7,2),(7,3),(7,4),(9,1),(25,2),(35,2)):
        fact = factorial(d+1)
        require(gcd(fact,n) == 1, 'factorial hypothesis')
        inv = pow(fact,-1,n); count = 0
        for c in sorted(set((0,1,2,n-1))):
            f = tuple(c*inv*pow(x,d+1,n) % n for x in range(n))
            for inc in product(range(n),repeat=d):
                h = f; slope = c
                for a in inc:
                    h = phase_difference(h,a,n); slope = slope*a % n
                require(all(h[x] == (slope*x+h[0]) % n for x in range(n)), 'backward factorial leading sign')
                count += 1
        rows.append(dict(N=n,d=d,factorial_inverse=inv,coefficient_increment_cases=count))
    return rows


def check_exact_fourier():
    normalization = []
    for n,d in ((2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,1)):
        f = tuple(Q(x+1,n+1)*root(n, x*x+1) for x in range(n))
        cube = q_cube(f,d+2)
        square = q_squared(f,d+2)
        fourth = Cyclo(n)
        for inc in product(range(n),repeat=d):
            h = iterated(f,inc); coeffs = fourier(h)
            require(sum((a.norm_square() for a in coeffs),Cyclo(n)) ==
                    mean(tuple(a.norm_square() for a in h)), 'exact Parseval')
            fourth = fourth+sum((a.norm_square()*a.norm_square() for a in coeffs),Cyclo(n))
        fourth = fourth/n**d
        require(cube == square == fourth, 'exact cube/derivative/Fourier normalization')
        require(cube == cube.conjugate(), 'real cube average')
        normalization.append(dict(N=n,d=d,cyclotomic_coefficients=cube.serialized()))
    energy = []
    for n,d in ((3,1),(5,1),(5,2),(7,1),(7,2)):
        c = 2; inv = pow(factorial(d+1),-1,n)
        q = tuple(root(n,c*inv*pow(x,d+1,n)) for x in range(n))
        v = tuple(root(n,(x*x*x+2*x+1) % n) for x in range(n))
        w = tuple(a*b.conjugate() for a,b in zip(v,q))
        selected = Cyclo(n); demodulated = Cyclo(n)
        for inc in product(range(n),repeat=d):
            slope = c
            for a in inc:
                slope = slope*a % n
            hv = iterated(v,inc); hw = iterated(w,inc)
            e = fourier(hv)[slope].norm_square(); m = mean(hw).norm_square()
            require(e == m, 'exact pointwise demodulated energy')
            selected = selected+e; demodulated = demodulated+m
        require(selected == demodulated, 'exact averaged demodulated energy')
        energy.append(dict(N=n,d=d,tuples=n**d,selected_energy=(selected/n**d).serialized()))
    # Disk return identity over Q(i), with no trigonometric floating arithmetic.
    disk = 0
    for rho in (Q(0),Q(1,7),Q(1,2),Q(6,7),Q(1)):
        for j,k in product(range(4),repeat=2):
            v = root(4,j); W = root(4,k)
            left = (rho*v-W).norm_square()
            right = rho*(v-W).norm_square()+(1-rho)**2
            require(left == right, 'exact disk return identity')
            upper = (v-W).norm_square()+1-rho
            diff = upper-left
            require(diff.a[1] == 0 and diff.a[0] >= 0, 'exact disk return inequality')
            disk += 1
    return dict(normalization_cases=normalization,energy_cases=energy,disk_return_cases=disk)


# Rational polynomials use low-to-high Fraction coefficients. The private
# arithmetic helpers receive only validated exact data from the bounded entry
# points below; in particular no binary floating-point conversion is used.
def _poly_trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p)


def _poly_add(p, q):
    return _poly_trim(tuple((p[i] if i < len(p) else Q(0)) +
                           (q[i] if i < len(q) else Q(0))
                           for i in range(max(len(p),len(q)))))


def _poly_scale(p, c):
    return _poly_trim(tuple(c*a for a in p))


def _poly_mul(p, q):
    out = [Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            out[i+j] += a*b
    return _poly_trim(out)


def _poly_shift(p, a):
    return _poly_trim(tuple(sum((p[j]*comb(j,i)*a**(j-i)
                                for j in range(i,len(p))),Q(0))
                           for i in range(len(p))))


def _poly_value(p, x):
    out = Q(0)
    for a in reversed(p):
        out = out*x+a
    return out


def _poly_backward(p, a):
    return _poly_add(p,_poly_scale(_poly_shift(p,-a),-1))


def _binomial_poly(j, scale_x=Q(1)):
    p = (Q(1),)
    for i in range(j):
        p = _poly_scale(_poly_mul(p,(-Q(i),scale_x)),Q(1,i+1))
    return p


def integer_binomial(x, j):
    """Integer-valued binomial polynomial, including negative integer x."""
    bounded(x,-128,128,'x'); bounded(j,0,9,'j')
    out = Q(1)
    for i in range(j):
        out *= Q(x-i,i+1)
    require(out.denominator == 1,'integer binomial integrality')
    return out.numerator


def _lift_parameters(n, m, c):
    bounded(n,2,14,'N'); bounded(m,1,9,'m'); bounded(c,-128,128,'c')


def rational_lift(n, m, c):
    """Solve P(x+N)-P(x)=c binom(x,m-1), P(0)=0, triangularly."""
    _lift_parameters(n,m,c)
    rhs = _poly_scale(_binomial_poly(m-1),c)
    a = [Q(0)]*(m+1)
    for r in range(m-1,-1,-1):
        remainder = sum((a[j]*comb(j,r)*n**(j-r)
                         for j in range(r+2,m+1)),Q(0))
        a[r+1] = ((rhs[r] if r < len(rhs) else Q(0))-remainder)/((r+1)*n)
    return _poly_trim(a)


def newton_lift(n, m, c):
    """Independent Newton-basis integration of F(t)=c binom(Nt,m-1)."""
    _lift_parameters(n,m,c)
    out = (Q(0),)
    for j in range(m):
        beta = sum((-1)**(j-i)*comb(j,i)*integer_binomial(n*i,m-1)
                   for i in range(j+1))
        out = _poly_add(out,_poly_scale(_binomial_poly(j+1,Q(1,n)),c*beta))
    return out


def _exact_rational(value):
    if (type(value) not in (int,Q) or abs(value.numerator).bit_length() > 256
            or value.denominator.bit_length() > 256):
        raise ValueError('bounded exact rational required')
    return Q(value)


def _rational_values(values):
    if type(values) not in (tuple,list) or not 2 <= len(values) <= 14:
        raise ValueError('bounded rational phase sequence required')
    out = []
    for item in values:
        if type(item) not in (tuple,list) or len(item) != 2:
            raise ValueError('amplitude and phase pairs required')
        amplitude, phase = map(_exact_rational,item)
        if abs(amplitude) > 2:
            raise ValueError('amplitude outside its exact bounded domain')
        out.append((amplitude,phase % 1))
    return tuple(out)


def _rational_differences(values, increments):
    n = len(values)
    for a in increments:
        values = tuple((values[x][0]*values[(x-a)%n][0],
                        (values[x][1]-values[(x-a)%n][1]) % 1)
                       for x in range(n))
    return values


def rational_differences(values, increments):
    values = _rational_values(values)
    if type(increments) not in (tuple,list) or len(increments) > 8:
        raise ValueError('at most eight bounded integer increments required')
    for a in increments:
        bounded(a,-128,128,'increment')
    return _rational_differences(values,increments)


def _phase_put(total, phase, weight):
    if weight:
        phase %= 1
        total[phase] = total.get(phase,Q(0))+weight
        if not total[phase]:
            del total[phase]


def rational_selected_energy(values, d, c, sign=1):
    """Formal selected Fourier energy in Q[Q/Z]; sign=-1 is a control."""
    values = _rational_values(values); n = len(values)
    bounded(d,1,4,'d'); bounded(c,-128,128,'c')
    if type(sign) is not int or sign not in (-1,1):
        raise ValueError('Fourier sign must be -1 or 1')
    if n > 6 or n**(d+2) > 4096:
        raise ValueError('selected energy work budget exceeded')
    total = {}
    for increments in product(range(n),repeat=d):
        h = _rational_differences(values,increments)
        slope = Q(sign*c*prod(increments),n)
        for x,y in product(range(n),repeat=2):
            _phase_put(total,h[x][1]-h[y][1]-slope*(x-y),
                       h[x][0]*h[y][0]/n**(d+2))
    return total


def rational_cube(values, k):
    """Direct formal cube expansion, independent of the derivative routine."""
    values = _rational_values(values); n = len(values)
    bounded(k,1,5,'k')
    if n > 6 or n**(k+1)*2**k > 65536:
        raise ValueError('direct cube work budget exceeded')
    total = {}
    vertices = tuple((omega,(-1)**sum(omega)) for omega in product((0,1),repeat=k))
    for increments in product(range(n),repeat=k):
        for x in range(n):
            phase, amplitude = Q(0), Q(1)
            for omega, sign in vertices:
                y = (x-sum(a*b for a,b in zip(increments,omega))) % n
                amplitude *= values[y][0]
                phase += sign*values[y][1]
            _phase_put(total,phase,amplitude/n**(k+1))
    return total


def check_rational_lifts():
    counts = dict(binomial_values=0,negative_binomial_identities=0,polynomials=0,
                  integer_shift_values=0,point_representative_checks=0,
                  signed_integer_derivatives=0,cyclic_derivative_values=0,
                  increment_representative_checks=0,lift_change_polynomials=0,
                  lift_change_values=0)
    for x,j in product(range(-32,33),range(10)):
        b = integer_binomial(x,j)
        require(Q(b) == _poly_value(_binomial_poly(j),x),'binomial polynomial value')
        if x < 0:
            require(b == (-1)**j*comb(-x+j-1,j),'negative binomial identity')
            counts['negative_binomial_identities'] += 1
        counts['binomial_values'] += 1
    for n,m in product(range(2,13),range(2,8)):
        for c in sorted(set((-2,-1,0,1,2,n-1,n,n+1))):
            p = rational_lift(n,m,c)
            require(p == newton_lift(n,m,c),'triangular versus Newton lift')
            require(p[0] == 0,'normalized rational constant')
            require((p[m] if len(p) > m else Q(0)) == Q(c,factorial(m)*n),
                    'rational leading coefficient')
            require(_poly_add(_poly_shift(p,n),_poly_scale(p,-1)) ==
                    _poly_scale(_binomial_poly(m-1),c),'prescribed rational shift')
            for x in range(-2*n-3,2*n+4):
                jump = _poly_value(p,x+n)-_poly_value(p,x)
                require(jump == c*integer_binomial(x,m-1) and jump.denominator == 1,
                        'integer shift including negative representatives')
                counts['integer_shift_values'] += 1
                for t in (-3,-1,0,1,2):
                    require((_poly_value(p,x+t*n)-_poly_value(p,x)).denominator == 1,
                            'arbitrary point representative')
                    counts['point_representative_checks'] += 1
            d = m-1
            # Nine recipes per polynomial; repeated tuples count as repeated
            # checks. Include negative, zero, nonzero multiples of N and mixed signs.
            increments = [(a,)*d for a in (-n-1,-n,-1,0,1,n,n+1)]
            increments += [tuple((-1)**j*(j+1) for j in range(d)),
                           tuple(n+j+1 for j in range(d))]
            values = tuple((Q(1),_poly_value(p,x)%1) for x in range(n))
            for inc in increments:
                derivative = p
                for a in inc:
                    derivative = _poly_backward(derivative,a)
                slope = Q(c*prod(inc),n)
                require(derivative == _poly_trim((derivative[0],slope)),
                        'signed rational derivative and positive slope')
                counts['signed_integer_derivatives'] += 1
                h = _rational_differences(values,inc)
                for x in range(n):
                    require(h[x] == (Q(1),_poly_value(derivative,x)%1),
                            'cyclic derivative including scalar')
                    require((h[x][1]-h[0][1]-slope*x).denominator == 1,
                            'cyclic rational character')
                    counts['cyclic_derivative_values'] += 1
                for j in range(d):
                    for shift in (-n,n):
                        alias = list(inc); alias[j] += shift
                        require(_rational_differences(values,alias) == h,
                                'increment representative independence')
                        counts['increment_representative_checks'] += 1
            for t in (-1,1):
                delta = _poly_add(rational_lift(n,m,c+t*n),_poly_scale(p,-1))
                reduced = _poly_add(delta,_poly_scale(_binomial_poly(m),-t))
                require(len(reduced) <= m,'integer lift change has lower circle degree')
                counts['lift_change_polynomials'] += 1
                for x in (-n-1,-1,0,1,n+1):
                    require((_poly_value(delta,x)-_poly_value(reduced,x)).denominator == 1,
                            'integer lift change modulo integer-valued polynomial')
                    require((_poly_value(reduced,x+n)-_poly_value(reduced,x)).denominator == 1,
                            'lower-degree lift change remains periodic')
                    counts['lift_change_values'] += 1
            counts['polynomials'] += 1
    example = (Q(0),Q(5,12),Q(-3,8),Q(1,12))
    require(rational_lift(2,3,1) == newton_lift(2,3,1) == example,'N2 cubic coefficients')
    derivative = _poly_backward(_poly_backward(example,1),1)
    require(derivative == (Q(-5,4),Q(1,2)),'N2 cubic backward derivative')
    require(_poly_value(example,1) == Q(1,8),'N2 cubic torsion value')
    lift_change = (_poly_value(rational_lift(2,3,3),1)-_poly_value(example,1))%1
    require(lift_change == Q(1,4),'integer lift can change the circle phase')
    torsion = []
    for d in range(1,9):
        p = rational_lift(2,d+1,1)
        require(p == newton_lift(2,d+1,1),'torsion Newton agreement')
        require(_poly_value(p,1) == Q((-1)**d,2**(d+1)),'torsion conjugation parity')
        values = tuple((Q(1),_poly_value(p,x)%1) for x in range(2))
        h = _rational_differences(values,(1,)*d)
        require((h[1][1]-h[0][1])%1 == Q(1,2),'torsion rational slope')
        for inc in product(range(2),repeat=d+2):
            require(_rational_differences(values,inc) == ((Q(1),Q(0)),)*2,
                    'rational torsion exact extremizer')
        torsion.append(dict(d=d,lift_value_at_1_mod_1=str(_poly_value(p,1)%1),
                            original_example_value_at_1=str(Q(1,2**(d+1))),
                            top_order_tuples=2**(d+2)))
    return dict(arithmetic='Fraction coefficients only; bounded diagnostics, not universal proof',
                ranges=dict(N=[2,12],m=[2,7],c='sorted set {-2,-1,0,1,2,N-1,N,N+1}',
                            binomial_x=[-32,32],binomial_j=[0,9],
                            point_x='-2*N-3 through 2*N+3 inclusive',point_shift_multiples=[-3,-1,0,1,2],
                            increment_recipes='seven constant tuples (-N-1,-N,-1,0,1,N,N+1); '
                            '((-1)^j*(j+1)) and (N+j+1), j=0..m-2; duplicates counted',
                            increment_alias_shifts='-N and +N in each coordinate',
                            coefficient_lift_shifts='-N and +N',
                            lift_change_x='-N-1,-1,0,1,N+1'),
                counts=counts,N2_cubic_coefficients=list(map(str,example)),
                N2_cubic_second_difference=list(map(str,derivative)),
                N2_c1_to_c3_phase_change_at_1=str(lift_change),torsion_cases=torsion)


def check_rational_energy():
    families = ((2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),
                (4,1),(4,2),(4,3),(6,1),(6,2))
    rows = []; mismatches = 0
    for n,d in families:
        for c in sorted(set((0,1,n-1))):
            p = rational_lift(n,d+1,c)
            for unit in (False,True):
                values = tuple((Q(1) if unit else Q((2*x+1)%4,3),Q(x*x+3*x+1,11)%1)
                               for x in range(n))
                w = tuple((a,(phase-_poly_value(p,x))%1) for x,(a,phase) in enumerate(values))
                energy = rational_selected_energy(values,d,c)
                require(energy == rational_cube(w,d+1),'rational selected energy equals direct cube')
                mismatch = rational_selected_energy(values,d,c,sign=-1) != energy
                mismatches += mismatch
                rows.append(dict(N=n,d=d,c=c,unit_input=unit,formal_phase_terms=len(energy),
                                 wrong_sign_formal_mismatch=mismatch,
                                 selected_pair_terms=n**(d+2),direct_cube_terms=n**(d+2)))
    require(mismatches == 32,'wrong Fourier sign formal negative controls')
    # Formal inequality need not imply inequality after evaluation at complex
    # roots. This separate Q[z]/Phi_3 witness verifies an actual wrong-sign failure.
    v = tuple(root(3,-x*x) for x in range(3))
    positive = sum((fourier(difference(v,a))[a].norm_square() for a in range(3)),Cyclo(3))/3
    wrong = sum((fourier(difference(v,a))[(-a)%3].norm_square() for a in range(3)),Cyclo(3))/3
    require(positive == 1 and wrong == Q(1,3),'wrong Fourier sign exact cyclotomic witness')
    stages = 0
    for k in range(2,31):
        r = k-2; A = (2**k+1)*6**(r*(r+1)//2); epsilon = Q(3,10*A)
        delta = A*epsilon
        require(delta == Q(3,10) and delta/6**(r*(r+1)//2) == (2**k+1)*epsilon,
                'rational descent endpoint')
        for d in range(1,r+1):
            t = delta/6**(d*(d+1)//2)
            require(6**d*t == delta/6**((d-1)*d//2),'rational descent recurrence')
            require(20*6**(d-1)*t == Q(1,6**(d*(d-1)//2)) <= 1,
                    'rational descent admissibility')
            stages += 1
    return dict(arithmetic='Exact energy identity in Q[Q/Z], without numerical roots or tolerance',
                families=[list(pair) for pair in families],c='sorted set {0,1,N-1}',
                unit_amplitude='1',nonunit_amplitude='((2*x+1) mod 4)/3',
                input_phase='(x*x+3*x+1)/11 modulo 1',cases=rows,case_count=len(rows),
                wrong_sign_formal_mismatch_cases=mismatches,
                wrong_sign_cyclotomic_witness=dict(N=3,d=1,c=1,selected_energy='1',wrong_sign_energy='1/3'),
                descent_k_range=[2,30],positive_descent_stages=stages)


def check_sources():
    manifest = json.loads((ROOT/'provenance/source_manifest.json').read_text())
    expected = {
        'Definitions.lean': ('17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b', '97113b7afa6925a2dd4b76641eeaeff09597ab6a'),
        'Mathlib_Fourier_ZMod.lean': ('0735a2370e6a0fb62fed50660757914a01400c19b6f66a1d768c71b907d972c9','101a428d82866a93cba10e85c589fe38864a212e'),
        'lake-manifest.json': ('95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665','dc6d553da8d0ca6a9ad926545920d21f9dc6b4c7')}
    locations = {
        'Definitions.lean': ('VladimirReshetnikov/ProveIt',
            'Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean'),
        'Mathlib_Fourier_ZMod.lean': ('leanprover-community/mathlib4',
            'Mathlib/Analysis/Fourier/ZMod.lean'),
        'lake-manifest.json': ('VladimirReshetnikov/ProveIt', 'lake-manifest.json')}
    require(type(manifest) is list and len(manifest) == 3, 'source manifest count')
    require({r['name'] for r in manifest} == set(expected), 'source manifest names')
    for row in manifest:
        repository, path = locations[row['name']]
        require((row['repository'], row['repository_path']) == (repository, path),
                'pinned source repository and path')
        data = (ROOT/'provenance/sources'/row['name']).read_bytes()
        sha = hashlib.sha256(data).hexdigest()
        git = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require((sha,git) == expected[row['name']], 'pinned source bytes')
        require(sha == row['sha256'] and git == row['git_blob_sha1'] and len(data) == row['bytes'], 'source manifest digests')
        commit = ('81a5d257c8e410db227a6665ed08f64fea08e997' if row['name'].startswith('Mathlib')
                  else '95460768cc4015862fec316f83df5861b04d28bc')
        require(row['commit'] == commit, 'source commit')
        require(row['url'] == 'https://github.com/'+repository+'/blob/'+commit+'/'+path, 'pinned source URL')
    lake = json.loads((ROOT/'provenance/sources/lake-manifest.json').read_text())
    require(any(p.get('name') == 'mathlib' and p.get('rev') == '81a5d257c8e410db227a6665ed08f64fea08e997'
                for p in lake['packages']), 'Mathlib dependency pin')
    return dict(snapshots=3,exact_sha256_and_git_blob_checks=True)


def run_all():
    return dict(status='PASS', report=284,
        scope='Exact bounded diagnostics only; universal proofs are in article.tex. No floating arithmetic.',
        constants=check_constants(),dense_maps=check_dense_maps(),support=check_support(),
        torsion=check_torsion(),descent=check_descent(),polynomial=check_polynomial(),
        exact_fourier=check_exact_fourier(),rational_lifts=check_rational_lifts(),
        rational_energy=check_rational_energy(),sources=check_sources())


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv:
        raise SystemExit('No command-line parameters are accepted; workloads are fixed and bounded.')
    print(json.dumps(run_all(),indent=2,sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
