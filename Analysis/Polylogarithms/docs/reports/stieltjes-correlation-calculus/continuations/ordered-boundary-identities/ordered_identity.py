#!/usr/bin/env python3
"""Evaluate the article's ordered two-particle sum at integer orders.

Examples:
  python ordered_identity.py 2 3
  python ordered_identity.py 2 2 --a 1 --b 2 --latex

This computes the proved finite polygamma formula. It does not numerically
sum the original double series. Shifts must be positive rational numbers;
the article treats the larger complex domain.
"""
import argparse
import sympy as s


def kernel(p, q, x, y):
    if x == y:
        return s.zeta(p + q, x)
    D = y - x
    A = {k: s.Integer(-1)**(p-k) * s.binomial(p+q-k-1, q-1)
         / D**(p+q-k) for k in range(1, p+1)}
    B = {k: s.Integer(-1)**p * s.binomial(p+q-k-1, p-1)
         / D**(p+q-k) for k in range(1, q+1)}
    assert A[1] + B[1] == 0
    return (A[1] * (s.digamma(y)-s.digamma(x))
            + sum(A[k]*s.zeta(k,x) for k in range(2,p+1))
            + sum(B[k]*s.zeta(k,y) for k in range(2,q+1)))


def ordered(p, q, a=s.Integer(1), b=s.Integer(1)):
    if p < 1 or q < 2:
        raise ValueError("The ordinary positive-order sum needs p>=1 and q>=2.")
    a, b = s.Rational(a), s.Rational(b)
    if a <= 0 or b <= 0:
        raise ValueError("This CLI accepts positive rational shifts.")
    E = (a**(-p)-(a+1)**(-p))/2
    return s.simplify(E*s.zeta(q,b+1)
                      +(kernel(p,q,a+2,b+1)-kernel(p,q,a,b+1))/4)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int)
    parser.add_argument("q", type=int)
    parser.add_argument("--a", default="1")
    parser.add_argument("--b", default="1")
    parser.add_argument("--latex", action="store_true")
    args = parser.parse_args()
    value = ordered(args.p, args.q, args.a, args.b)
    print(s.latex(value) if args.latex else value)


if __name__ == "__main__":
    main()
