"""Small exact multivariate polynomial checker (no symbolic dependencies)."""
from fractions import Fraction
from math import factorial
from support_kernels import bipartite_kernel_table

class Poly:
    def __init__(self, value=0, n=1):
        self.n = n
        self.terms = (dict(value) if isinstance(value, dict)
                      else {(0,)*n: Fraction(value)})
        self.terms = {k: Fraction(v) for k, v in self.terms.items() if v}
    @staticmethod
    def var(i, n):
        key = tuple(int(j == i) for j in range(n))
        return Poly({key: 1}, n)
    def coerce(self, other):
        return other if isinstance(other, Poly) else Poly(other, self.n)
    def __add__(self, other):
        other = self.coerce(other)
        d = self.terms.copy()
        for k, v in other.terms.items():
            d[k] = d.get(k, 0)+v
        return Poly(d, self.n)
    __radd__ = __add__
    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()}, self.n)
    def __sub__(self, other):
        return self + -self.coerce(other)
    def __rsub__(self, other):
        return self.coerce(other) + -self
    def __mul__(self, other):
        other = self.coerce(other)
        d = {}
        for a, u in self.terms.items():
            for b, v in other.terms.items():
                key = tuple(x+y for x, y in zip(a, b))
                d[key] = d.get(key, 0)+u*v
        return Poly(d, self.n)
    __rmul__ = __mul__
    def __truediv__(self, scalar):
        return self * Fraction(1, scalar)
    def __pow__(self, power):
        out = Poly(1, self.n)
        for _ in range(power):
            out = out*self
        return out
    def __eq__(self, other):
        return self.terms == self.coerce(other).terms
    def evaluate(self, point):
        total = Fraction(0)
        for exponents, value in self.terms.items():
            for x, e in zip(point, exponents):
                value *= x**e
            total += value
        return total

def choose_poly(p, k):
    out = Poly(1, p.n)
    for j in range(k):
        out *= p-j
    return out/factorial(k)

def symbolic_kernel(a, b, core, variables):
    ql, qr, terms = bipartite_kernel_table(a, b, core)
    result = [Poly(0, variables[0].n) for _ in range(a+b+1)]
    for i, j, k, multiplicity in terms:
        term = Poly(multiplicity, variables[0].n)
        for variable, quota in zip(variables, ql[i]+qr[j]):
            term *= choose_poly(variable, quota)
        result[k] += term
    return result

def verify_certificates():
    x, y, z, w, alpha, beta = [Poly.var(i, 6) for i in range(6)]
    A = x+y+2*z
    B = x*y+x*z+y*z+(z*z-z)/2
    C = alpha*(y+z)+beta*(x+z)-alpha*beta*z
    e = alpha+beta
    p1, p2, p3 = w+A+e, w*A+B+C, w*B
    lhs = p2*p2-3*p1*p3
    rhs = (A*w/2-(B+C))**2+3*(A*A-4*B)*w*w/4+3*(A*C-e*B)*w
    assert lhs == rhs
    assert A*A-4*B == (x-y)**2+2*z*(z+1)
    assert A*C-e*B == (alpha*(1-beta)*(y*y+2*y*z+(3*z*z+z)/2)
                       + beta*(1-alpha)*(x*x+2*x*z+(3*z*z+z)/2)
                       + alpha*beta*(x*x+y*y+x*z+y*z+z*z+z))
    for core in range(4):
        xx, yy, zz, ww = [Poly.var(i, 4) for i in range(4)]
        aa, bb = core & 1, (core >> 1) & 1
        AA = xx+yy+2*zz
        BB = xx*yy+xx*zz+yy*zz+(zz*zz-zz)/2
        CC = aa*(yy+zz)+bb*(xx+zz)-aa*bb*zz
        expected = [Poly(1, 4), ww+AA+aa+bb, ww*AA+BB+CC, ww*BB]
        assert symbolic_kernel(1, 2, core, [xx, yy, zz, ww]) == expected
    N = Poly.var(0, 1)
    fam = [Poly(1), 8*N+4, 23*N*N+11*N+1, 28*N**3+5*N*N,
           N*N*(7*N-1)**2/4]
    assert symbolic_kernel(2, 2, 15, [N]*6) == fam
    gaps = [k*(4-k)*fam[k]**2-(k+1)*(5-k)*fam[k-1]*fam[k+1]
            for k in range(1, 4)]
    assert gaps[0] == 8*(N*N+13*N+5)
    assert gaps[1] == 4*(25*N**4+164*N**3+122*N*N+22*N+1)
    assert gaps[2] == N*N*(98*N**4+406*N**3+239*N*N+6*N-2)
    t = N
    positive_shift = (98*(t+1)**4+406*(t+1)**3+239*(t+1)**2+6*(t+1)-2)
    assert all(c > 0 for c in positive_shift.terms.values())
    return {'rank_three_sos_identities': 3,
            'rank_three_symbolic_kernel_cases': 4,
            'rank_four_symbolic_kernel_cases': 1,
            'rank_four_gap_identities': 3,
            'last_gap_shift_coefficients':
                [int(positive_shift.terms.get((i,), 0)) for i in range(5)]}

if __name__ == '__main__':
    print(verify_certificates())
