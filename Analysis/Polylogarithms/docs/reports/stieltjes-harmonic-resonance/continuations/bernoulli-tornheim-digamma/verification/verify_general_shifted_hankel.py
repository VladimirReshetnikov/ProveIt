"""Exact finite diagnostics for sections/03b_general_hankel.tex; not its proof.

Uses the original binomial source entries, independently checks the
factorial factorization, and checks the small determinant formula.
"""
from pathlib import Path
import json
import sympy as s


def mu(n):
    return s.bernoulli(2*n)/s.factorial(2*n) if n >= 0 else s.S.Zero


def source_entry(a, b, t, k):
    d = 2*(b+t)+1
    e = d-2*a-2*b+2*k+1
    if e < 0:
        return s.S.Zero
    value = s.S.Zero
    for upper, lower in ((d-2*b+1, 2*a-2*k), (d-2*a+1, 2*b-2*k)):
        if 2 <= lower <= upper:
            value += s.binomial(upper, lower)/upper
    return s.bernoulli(e)*value


def coeff(n, t):
    if t > n:
        return s.S.Zero
    return 2*s.factorial(2*n+2*t+1)*s.factorial(2*n+1)/(s.factorial(4*n+2)*s.factorial(2*n-2*t+1)*s.factorial(2*t))


def h(n):
    return s.factorial(2*n+1)**2/(s.factorial(4*n+2)*s.factorial(4*n+3))


def c(n):
    return (2*n+1)*s.factorial(2*n+2)/s.factorial(4*n+2)


def f(ell, n):
    return s.prod((2*n-r)*(2*n+3+r) for r in range(2*ell))/s.factorial(2*ell+1)


def falling(x, d):
    return s.prod(x-r for r in range(d))


checks = []
for b in range(1, 10):
    for a in range(1, b+1):
        H = s.Matrix(b, b, lambda t, k: mu(t+k-a+1))
        R = s.diag(*(s.factorial(2*b+2*t-2*a+1) for t in range(b)))
        E = s.diag(*(1/s.factorial(2*b-2*k) for k in range(b)))

        def rho(t, k):
            return s.factorial(2*t+1)*s.factorial(2*b-2*k)/(s.factorial(2*a-2*k)*s.factorial(2*b+2*t-2*a+1))

        U = s.Matrix(b, b, lambda t, k: mu(t+k-a+1)*rho(t, k) if k < a else 0)
        M = s.Matrix(b, b, lambda t, k: source_entry(a, b, t, k))
        assert M == R*(H+U)*E
        assert U[:a, :a].det() != 0
        detH = H.det()
        expected_sign = (-1)**(a//2) if a % 2 == 0 else (-1)**(b-(a+1)//2)
        assert s.sign(detH) == expected_sign
        A = s.Matrix(a, a, lambda i, k: sum(coeff(b-a+i, t)*mu(t+k-a+1)*(1+rho(t, k)) for t in range(b-a+i+1)))
        scalar = (-1)**(a*(b-a))*s.prod(h(n) for n in range(b-a))
        assert M.det() == R.det()*E.det()*scalar*A.det()
        F = s.Matrix(a, a, lambda i, k: f(a-1-k, b-a+i))
        assert detH == scalar*s.prod(c(b-a+i) for i in range(a))*F.det()
        for i in range(a):
            n = b-a+i
            for k in range(a):
                ell = a-1-k
                perturbation = A[i, k]-c(n)*f(ell, n)
                if n < ell:
                    assert perturbation == 0
                    continue
                N = 2*(n-ell)+1
                prefactor = 2*s.factorial(2*n+1)*s.factorial(2*b-2*k)/(s.factorial(4*n+2)*s.factorial(2*a-2*k)*s.factorial(N))
                weighted = sum(s.binomial(N, 2*r)*s.bernoulli(2*r)*(2*r+2*ell+1)*falling(2*n+2*ell+2*r+1, 2*i) for r in range(n-ell+1))
                assert perturbation == prefactor*weighted
        checks.append({"a": a, "b": b, "det_H_sign": int(s.sign(detH)), "factorization": True, "small_determinant": True, "weighted_sum": True})

result = {"status": "PASS", "scope": "Exact finite diagnostics; proofs are in sections/03b_general_hankel.tex.", "checks": checks}
Path(__file__).resolve().parent.parent.joinpath("results", "verify_general_shifted_hankel.json").write_text(json.dumps(result, indent=2)+"\n")
print(f"PASS: original source coefficients, rank-a factorization, shifted-H signs, small determinants and weighted Bernoulli sums for {len(checks)} pairs 1<=a<=b<=9.")
