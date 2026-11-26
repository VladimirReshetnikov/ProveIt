#!/usr/bin/env python3
"""Exact, reproducible checks for the totally real S3 transfer example.

Requires Python 3 and SymPy.  These are arithmetic certificates, not a Lean
verification of the grh-lean project or a proof of a new norm inequality.
All matrix checks use exact rational arithmetic; primality below is checked
by elementary trial division, and polynomial operations are exact modulo p.
"""

import itertools
import json
import math
from pathlib import Path

import sympy as sp


def is_prime_trial(n):
    if n < 2:
        return False
    return all(n % k for k in range(2, math.isqrt(n) + 1))


def sign_bit(p):
    return sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)) % 2


def compose(p, q):
    return tuple(p[q[i]] for i in range(3))


def group_mul(a, b):
    return (compose(a[0], b[0]), (a[1] + b[1]) % 2, (a[2] + b[2]) % 5)


def main():
    x = sp.Symbol("x")
    f = sp.Poly(x**3 - 4*x + 1, x, domain=sp.QQ)
    assert f.eval(1) != 0 and f.eval(-1) != 0
    assert f.discriminant() == 229
    assert is_prime_trial(229)
    # Three disjoint sign-changing intervals certify total reality.
    intervals = [(-3, -2), (0, 1), (1, 2)]
    assert all(f.eval(a) * f.eval(b) < 0 for a, b in intervals)

    # Tr(1),...,Tr(alpha^4) follow from Newton sums for f.
    trace_powers = [3, 0, 8, -3, 32]
    T = sp.Matrix([[trace_powers[i+j] for j in range(3)] for i in range(3)])
    # Columns express 1, alpha, 24 alpha^2+9 alpha-64 in (1,alpha,alpha^2).
    U = sp.Matrix([[1, 0, -64], [0, 1, 9], [0, 0, 24]])
    D = U.T * T * U
    assert D == sp.diag(3, 8, 5496)
    bound_L = 5496
    mult_L = [1832, 687, 1]
    # With embedding matrix V, T=V^t V; hence this identity proves the frame.
    assert U * sp.diag(*mult_L) * U.T == bound_L * T.inv()

    # The S3 closure is F=L(sqrt(229)), with basis u and sqrt(229)u.
    norms_F = [6, 16, 10992, 1374, 3664, 2517168]
    bound_F = 48 * 229**2
    mult_F = [bound_F // n for n in norms_F]
    assert mult_F == [419528, 157323, 229, 1832, 687, 1]
    assert all(m * n == bound_F for m, n in zip(mult_F, norms_F))

    # Both primes have the same residue class modulo an admissible q0, but
    # different Frobenius classes in F.  They are also both inert in this K.
    q0 = 18480 * 229
    d = 167160839
    primes = [38087281, 59246881]
    assert is_prime_trial(d) and d % 8 == 7
    assert 2 * (d + 1) % q0 == 0 and (d + 1) % q0 != 0
    examples = []
    for p in primes:
        assert is_prime_trial(p) and p % q0 == 1
        assert pow((-d) % p, (p-1)//2, p) == p-1
        fp = sp.Poly(f.as_expr(), x, modulus=p)
        factors = fp.factor_list()[1]
        degrees = sorted(g.degree() for g, e in factors for _ in range(e))
        product = sp.Poly(1, x, modulus=p)
        for g, e in factors:
            product *= g**e
        assert product == fp
        frob_remainder = sp.Poly(pow_x_mod(p, fp), x, modulus=p)
        gcd = sp.gcd(frob_remainder - sp.Poly(x, x, modulus=p), fp)
        if degrees == [3]:
            # No F_p root implies irreducibility for a cubic.
            assert gcd.degree() == 0
        examples.append({
            "p": p,
            "p_mod_q0": p % q0,
            "factor_degrees": degrees,
            "factors": [{"coeffs_descending": [int(c) for c in g.all_coeffs()],
                         "multiplicity": e} for g, e in factors],
            "x_to_p_mod_f_coeffs": [int(c) for c in frob_remainder.all_coeffs()],
            "gcd_x_to_p_minus_x_with_f_coeffs": [int(c) for c in gcd.all_coeffs()],
            "legendre_minus_d": -1,
        })
    assert examples[0]["factor_degrees"] == [1, 1, 1]
    assert examples[1]["factor_degrees"] == [3]

    # Finite fiber-product model: Gamma=C2_sign x C2_conj x C5_tower;
    # G={(sigma,a,c,b): sign(sigma)=(-1)^a}, represented by (sigma,c,b).
    # This tests the same quotient/coset mechanism, not a number-field model.
    ident = (0, 1, 2)
    perms = list(itertools.permutations(range(3)))
    G = [(s, c, b) for s in perms for c in range(2) for b in range(5)]
    H = {(ident, 0, b) for b in range(5)}
    S = {(ident, 0, b) for b in (0, 1)}
    t = (ident, 1, 0)
    B = {group_mul(t, s) for s in S}
    tH = {group_mul(t, h) for h in H}
    correlations = [sum(group_mul(g, a) in B for a in H) for g in G]
    assert all(n == (len(B) if g in tH else 0) for g, n in zip(G, correlations))
    # Pullback selectors ignore whether an even permutation is identity.
    A_pullback = {g for g in G if sign_bit(g[0]) == 0 and g[1] == 0}
    B_pullback = {g for g in G if sign_bit(g[0]) == 0 and g[1] == 1 and g[2] in (0, 1)}
    g_id = (ident, 1, 0)
    g_cycle = ((1, 2, 0), 1, 0)
    pull_counts = [sum(group_mul(g, a) in B_pullback for a in A_pullback)
                   for g in (g_id, g_cycle)]
    sensitive_counts = [sum(group_mul(g, a) in B for a in H)
                        for g in (g_id, g_cycle)]
    assert pull_counts == [6, 6] and sensitive_counts == [2, 0]

    certificate = {
        "description": "Exact arithmetic and finite-group checks; no new global norm inequality claimed.",
        "polynomial": "x^3-4*x+1",
        "discriminant": 229,
        "three_real_root_intervals": intervals,
        "trace_gram_L": [list(map(int, row)) for row in T.tolist()],
        "orthogonal_basis_L": ["1", "alpha", "24*alpha^2+9*alpha-64"],
        "trace_norms_L": [3, 8, 5496],
        "frame_bound_L": bound_L,
        "frame_multiplicities_L": mult_L,
        "basis_F": ["1", "alpha", "24*alpha^2+9*alpha-64", "sqrt(229)",
                    "alpha*sqrt(229)", "(24*alpha^2+9*alpha-64)*sqrt(229)"],
        "trace_norms_F": norms_F,
        "frame_bound_F": bound_F,
        "frame_multiplicities_F": mult_F,
        "q0": q0,
        "d": d,
        "same_residue_different_frobenius": examples,
        "finite_group": {"order": len(G), "H_order": len(H), "B_order": len(B),
                         "all_coset_correlations_verified": True,
                         "pullback_identity_and_3cycle_counts": pull_counts,
                         "sensitive_identity_and_3cycle_counts": sensitive_counts},
        "all_checks_passed": True,
    }
    out = Path(__file__).resolve().parents[1] / "validation" / "nonabelian_frame.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(certificate, indent=2) + "\n")
    print(json.dumps({"all_checks_passed": True, "certificate": str(out),
                      "frame_bound_F": bound_F, "same_AP_primes": primes}, indent=2))


def pow_x_mod(n, f):
    """Binary exponentiation in F_p[x]/(f), using exact polynomial remainders."""
    x = f.gens[0]
    p = f.get_modulus()
    ans = sp.Poly(1, x, modulus=p)
    base = sp.Poly(x, x, modulus=p)
    while n:
        if n & 1:
            ans = (ans * base).rem(f)
        base = (base * base).rem(f)
        n //= 2
    return ans.as_expr()


if __name__ == "__main__":
    main()
