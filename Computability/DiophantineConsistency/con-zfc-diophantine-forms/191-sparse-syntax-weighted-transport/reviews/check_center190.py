#!/usr/bin/env python3
"""Independent exact center and norm-defect collection; standard library only."""
from collections import defaultdict
import json


class P:
    def __init__(self, values):
        self.p = {m: c for m, c in values.items() if c}

    @staticmethod
    def c(n):
        return P({(0,) * 6: n})

    def __add__(self, other):
        other = other if isinstance(other, P) else P.c(other)
        out = defaultdict(int, self.p)
        for m, c in other.p.items():
            out[m] += c
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.p.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other, P) else P.c(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, P) else P.c(other)
        out = defaultdict(int)
        for m, c in self.p.items():
            for n, d in other.p.items():
                out[tuple(a + b for a, b in zip(m, n))] += c * d
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        out, base = P.c(1), self
        while n:
            if n & 1:
                out = out * base
            n >>= 1
            if n:
                base = base * base
        return out

    def quotient_A(self, n):
        return P({(m[0]-n,) + m[1:]: c for m, c in self.p.items() if m[0] >= n})

    def divide_exact(self, d):
        if any(c % d for c in self.p.values()):
            raise ValueError('Nonintegral coefficient division')
        return P({m: c // d for m, c in self.p.items()})

    def top(self, weights):
        deg = max(sum(a*b for a, b in zip(m, weights)) for m in self.p)
        return deg, P({m: c for m, c in self.p.items()
                       if sum(a*b for a, b in zip(m, weights)) == deg})


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    A, Y, k, U, b, c = [P({tuple(int(i == j) for i in range(6)): 1})
                         for j in range(6)]
    e2 = k**2 * Y**2
    e1 = k**2 * Y * (1-2*Y-2*Y**2)
    e0 = 1 + k**2 * Y * (Y+1) * (Y*(Y+1)-1)
    E = e2*A**2 + e1*A + e0
    Delta = A**2 - 1
    V = (1 + 2*Delta*U**2*E)*b-c
    G = E*(1 + Delta*U**2*E)
    S = e2*A + e1
    theta = U**2*b
    Omega = U*(2*S*(theta*(3*E+e2)-(b-c))
               + A*(4*E*V-theta*(4*E**2+3*S**2+e2**2)))
    F = E*V
    quotient_center = U*(4*A*F-2*F.quotient_A(1)
                        -F.quotient_A(3).divide_exact(2))
    require(Omega.p == quotient_center.p, 'Center identity failed')
    defect = Omega**2 - 16*G*V**2
    weights = (4, 2, 1, 5, 4, 2)
    center_degree, _ = Omega.top(weights)
    defect_degree, defect_top = defect.top(weights)
    expected = 8*A**6*Y**8*k**8*U**6*b**2*(A**2-6*Y**4)
    require(defect_top.p == expected.p, 'Defect top form failed')
    require(len(Omega.p) == 84, 'Unexpected center support')
    require(len(defect.p) == 594, 'Unexpected defect support')
    require(center_degree == 59 and defect_degree == 94, 'Unexpected degree')
    print(json.dumps({
        'status': 'PASS',
        'variables': ['A','Ybar','k','U','b','c'],
        'weights': weights,
        'center_terms': len(Omega.p),
        'center_degree': center_degree,
        'defect_terms': len(defect.p),
        'defect_degree': defect_degree,
        'defect_top_terms': [[coeff, list(mon)] for mon, coeff
                             in sorted(defect_top.p.items())],
        'checks': ['integer quotient-center identity',
                   'exact expanded norm defect',
                   'full weighted leading form'],
    }, indent=2))


if __name__ == '__main__':
    main()
