"""Check the pentad identity using only Python's exact integers.

Polynomials are sparse dictionaries from exponent quadruples to coefficients.
No computer algebra package, external solver, or stored verdict is trusted.
"""
from __future__ import annotations
from dataclasses import dataclass


@dataclass
class P:
    terms: dict[tuple[int, int, int, int], int]

    @staticmethod
    def constant(n: int) -> P:
        return P({(0, 0, 0, 0): n} if n else {})

    def __add__(self, other: P | int) -> P:
        other = P.constant(other) if isinstance(other, int) else other
        out = dict(self.terms)
        for exponent, coefficient in other.terms.items():
            out[exponent] = out.get(exponent, 0) + coefficient
        return P({e: c for e, c in out.items() if c})

    __radd__ = __add__

    def __neg__(self) -> P:
        return P({e: -c for e, c in self.terms.items()})

    def __sub__(self, other: P | int) -> P:
        return self + (-other if isinstance(other, P) else -other)

    def __mul__(self, other: P | int) -> P:
        other = P.constant(other) if isinstance(other, int) else other
        out: dict[tuple[int, int, int, int], int] = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                g = tuple(x + y for x, y in zip(e, f))
                out[g] = out.get(g, 0) + c * d
        return P({e: c for e, c in out.items() if c})

    __rmul__ = __mul__


def main() -> None:
    a, b, c, d = [P({tuple(int(i == j) for j in range(4)): 1}) for i in range(4)]
    F = [-a*b+b*d-c*d+c, -a*b+a*c-c*d+d,
         -a*b+a*d+b-c*d, -a*b+a+b*c-c*d]
    H = [-(a*a*b-a*a*c+a*b-a-b*c+b+2*c*d-2*d),
         a*a-a*b*b+a*b*c+a*b-a*c+b*b-2*b*d,
         (b-1)*(a*b-a*c+a-c), (a*a+1)*(b-c)]
    lhs = sum((h*f for h, f in zip(H, F)), P.constant(0))
    rhs = 2*c*(c-1)*d*(d-1)
    if (lhs-rhs).terms:
        raise ArithmeticError('Certificate identity failed.')
    print('PASS: sum H_i F_i = 2 c(c-1)d(d-1), over Z[a,b,c,d].')
    print('Remaining nonzero coefficients:', len((lhs-rhs).terms))


if __name__ == '__main__':
    main()
