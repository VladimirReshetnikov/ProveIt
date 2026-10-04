#!/usr/bin/env python3
"""Independent arithmetic-only checks. No signal-machine simulator or imports.

Finite regressions support, but do not replace, AUDIT.md's proofs.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json


def sign(x):
    return (x > 0) - (x < 0)


def positive_root_test(alpha, beta, a, b, strict):
    assert alpha >= beta >= 0
    if alpha == 0:
        return False if strict else a >= 0 and b >= 0
    if beta == 0:
        return (a > 0 and b > 0) if strict else a >= 0 and b >= 0
    initial = a > 0 if strict else a >= 0
    return initial and b - beta * a >= 0


def real_root_test(r, s, a, b, strict):
    trace, det = r + s, r * s
    c = trace * b - det * a
    d = trace * c - det * b
    alpha, beta = sorted((r * r, s * s), reverse=True)
    return positive_root_test(alpha, beta, a, c, strict) and positive_root_test(
        alpha, beta, b, d, strict
    )


def sequence(trace, det, a, b, length):
    out = [a, b]
    for _ in range(2, length):
        out.append(trace * out[-1] - det * out[-2])
    return out[:length]


def radical_sign_by_cases(L, H, D):
    """Sign of L+H sqrt(D), using only rational polynomial sign tests."""
    assert D > 0
    if H == 0:
        return sign(L)
    if L == 0:
        return sign(H)
    if sign(L) == sign(H):
        return sign(L)
    return sign(L) * sign(L * L - D * H * H)


def radical_sign_by_isolation(L, H, D):
    """Separate oracle: exact rational intervals, handling equality first."""
    if H == 0:
        return sign(L)
    if L * L == D * H * H and L * H < 0:
        return 0
    scale = 1
    while True:
        scale *= 10
        k = isqrt((D.numerator * scale * scale) // D.denominator)
        lo, hi = F(k, scale), F(k + 1, scale)
        values = (L + H * lo, L + H * hi)
        if min(values) > 0:
            return 1
        if max(values) < 0:
            return -1


def quad(x):
    return x * x - 2


def compiler_residuals(g, selectors, copies, slacks):
    """Disjoint union: branch 0 g^2-2<0; branch 1 g^2-2>0.

    Both branches intentionally have a nonzero constant polynomial term.
    With natural g there are exactly two permissible sign branches and no
    integer root. All inactive private coordinates must be uniquely zero.
    """
    e0, e1 = selectors
    x0, x1 = copies
    z0, z1 = slacks
    L0 = quad(x0) - quad(0) * (1 - e0)
    L1 = quad(x1) - quad(0) * (1 - e1)
    return (
        e0 + e1 - 1,
        x0 - e0 * g,
        x1 - e1 * g,
        -L0 - e0 - z0,
        L1 - e1 - z1,
    )


def sign_gadget(Q, em, e0, ep, z):
    return (
        em * (em - 1), e0 * (e0 - 1), ep * (ep - 1),
        em + e0 + ep - 1,
        Q - (ep - em) * (z + 1), e0 * z,
    )


def positive_subsequence_summable(alpha, beta, a, b):
    assert positive_root_test(alpha, beta, a, b, True)
    if alpha == beta:
        return alpha < 1
    if beta == 0:
        return alpha < 1
    if alpha < 1:
        return True
    if beta >= 1:
        return False
    return b - beta * a == 0


def main():
    counts = {}
    roots = [F(-2), F(-1), F(-1, 2), F(0), F(1, 2), F(1), F(2)]
    assignments = 0
    for i, r in enumerate(roots):
        for s in roots[: i + 1]:
            for a0, b0 in product(range(-3, 4), repeat=2):
                a, b = F(a0), F(b0)
                values = sequence(r + s, r * s, a, b, 128)
                for strict in (False, True):
                    predicted = real_root_test(r, s, a, b, strict)
                    finite = all(v > 0 if strict else v >= 0 for v in values)
                    # For this finite grid every failure has appeared by 128.
                    assert predicted == finite, (r, s, a, b, strict)
                    assignments += 1
    counts['real_recurrence_strict_and_weak_cases'] = assignments

    radical_cases = 0
    for D in [F(1), F(2), F(3), F(5), F(1, 2), F(2, 3), F(9, 4)]:
        for L0, H0 in product(range(-8, 9), repeat=2):
            L, H = F(L0, 3), F(H0, 5)
            assert radical_sign_by_cases(L, H, D) == radical_sign_by_isolation(L, H, D)
            radical_cases += 1
    counts['radical_sign_cases'] = radical_cases

    # Near-equal positive roots can postpone the first violation arbitrarily.
    # This deliberately refutes any universal finite-prefix shortcut.
    r, s = F(10001, 10000), F(1)
    a, b = F(1), F(9999, 10000)
    values = sequence(r + s, r * s, a, b, 7000)
    first_nonpositive = next(i for i, value in enumerate(values) if value <= 0)
    assert first_nonpositive > 1000
    assert not real_root_test(r, s, a, b, True)
    counts['late_first_nonpositive_index'] = first_nonpositive

    compiler_zeros = 0
    compiler_trials = 0
    for g in range(6):
        zeros = []
        # The equality sum(e)=1 narrows selectors exactly, not heuristically.
        for selectors in ((0, 1), (1, 0)):
            for copies in product(range(7), repeat=2):
                for slacks in product(range(25), repeat=2):
                    residuals = compiler_residuals(g, selectors, copies, slacks)
                    compiler_trials += 1
                    if all(v == 0 for v in residuals):
                        zeros.append((selectors, copies, slacks))
        assert len(zeros) == 1, (g, zeros)
        selected = (1, 0) if quad(g) < 0 else (0, 1)
        assert zeros[0][0] == selected
        compiler_zeros += len(zeros)
    counts['private_copy_candidate_assignments'] = compiler_trials
    counts['private_copy_unique_fibers'] = compiler_zeros

    sign_trials = 0
    for Q in range(-20, 21):
        zeros = []
        for em, e0, ep in product(range(3), repeat=3):
            for z in range(21):
                sign_trials += 1
                if not any(sign_gadget(Q, em, e0, ep, z)):
                    zeros.append((em, e0, ep, z))
        assert zeros == [(int(Q < 0), int(Q == 0), int(Q > 0), max(0, abs(Q) - 1))]
    counts['canonical_sign_gadget_candidates'] = sign_trials
    counts['canonical_sign_gadget_unique_fibers'] = 41

    clock_cases = clock_sums = hidden_cancellations = 0
    for i, r in enumerate(roots):
        for s in roots[: i + 1]:
            for a0, b0 in product(range(-3, 4), repeat=2):
                a, b = F(a0), F(b0)
                if not real_root_test(r, s, a, b, True):
                    continue
                u0, u1, u2, u3 = sequence(r + s, r * s, a, b, 4)
                alpha, beta = sorted((r * r, s * s), reverse=True)
                predicted = positive_subsequence_summable(alpha, beta, u0, u2) and positive_subsequence_summable(alpha, beta, u1, u3)
                if r != s:
                    cr, cs = (b - s * a) / (r - s), (r * a - b) / (r - s)
                    reference = (cr == 0 or abs(r) < 1) and (cs == 0 or abs(s) < 1)
                    exact_sum = sum(c / (1 - root) for c, root in ((cr, r), (cs, s)) if c != 0) if reference else None
                else:
                    reference = abs(r) < 1
                    assert r != 0  # Nilpotent recurrence cannot be strictly positive forever.
                    exact_sum = a / (1 - r) + (b / r - a) * r / (1 - r) ** 2 if reference else None
                assert predicted == reference
                clock_cases += 1
                if not predicted:
                    continue
                t, h = r * r + s * s, r * r * s * s
                den = 1 - t + h
                emitted_sum = (u2 + u3 + (1 - t) * (u0 + u1)) / den if den != 0 else (u0 + u1) / (2 - t)
                assert emitted_sum == exact_sum
                clock_sums += 1
                hidden_cancellations += max(abs(r), abs(s)) >= 1
    counts['positive_clock_classification_cases'] = clock_cases
    counts['rational_clock_sum_cases'] = clock_sums
    counts['stable_clock_with_unstable_full_spectrum_cases'] = hidden_cancellations

    # Formal clock/return arithmetic only; no event-driven physical simulation.
    spectator_cases = 0
    for d0 in range(1, 10):
        d = F(d0)
        for K in range(1, 11):
            threshold = d * (1 - F(1, 4) ** K) / 2
            for y in (threshold - F(1, 100), threshold, threshold + F(1, 100), d / 2):
                dn, yn, total = d, y, F(0)
                all_guards = True
                for _ in range(K):
                    all_guards &= dn > 0 and yn > 3 * dn / 8
                    total += 3 * dn / 8
                    dn, yn = dn / 4, yn - 3 * dn / 8
                assert all_guards == (y > threshold)
                assert dn == d * F(1, 4) ** K
                assert yn == y - threshold
                assert total == threshold
                spectator_cases += 1
    counts['spectator_return_algebra_cases'] = spectator_cases

    # Visible eigenvalue 1/4, hidden eigenvalue 1: radius is not a clock test.
    def mul(M, v):
        return tuple(sum(a * b for a, b in zip(row, v)) for row in M)
    M = ((F(1, 4), F(0)), (F(-3, 8), F(1)))
    for d, y in product(range(1, 7), repeat=2):
        v = (F(d), F(y))
        for n in range(12):
            assert 3 * v[0] / 8 == F(3 * d, 8) * F(1, 4) ** n
            v = mul(M, v)
    counts['hidden_unit_eigenvalue_clock_terms'] = 6 * 6 * 12

    result = {
        'status': 'PASS',
        'scope': 'Fresh exact-rational recurrence, radical, compiler, and return-map arithmetic only. No upstream program or physical simulator executed.',
        'counts': counts,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
