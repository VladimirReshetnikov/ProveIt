#!/usr/bin/env python3
"""Exact regression fixtures for the independent all-base-pooling proof.

These checks do not prove the unbounded theorem.  They check its algebra,
signed-index congruences, zero-base convention, orientation, constructive
inverse, and genuinely enormous-frame numerical examples.
"""
from fractions import Fraction
from itertools import product
import json
import random


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pell(A, k):
    X, Y = 1, 0
    for _ in range(abs(k)):
        X, Y = A * X + (A * A - 1) * Y, X + A * Y
    return X, Y if k >= 0 else -Y


def energy(A, n, requests):
    T = 2 * A * n - n * n - 1
    H = S = D = YY = 0
    for k, m in requests:
        X, Y = pell(A, k)
        U = X - A * Y
        H += Y * (m - X)
        S += (m - U) ** 2 - Y * Y
        D += (m - U - n * Y) ** 2
        YY += Y * Y
    E = S - 2 * n * H
    require(D == E - T * YY, 'Pell-error polynomial identity')
    return T, E, D


def main():
    counts = {'algebra': 0, 'signed_congruences': 0,
              'large_frames': 0, 'zero_base_controls': 0,
              'constructive_inverses': 0}
    # The algebra is valid without any size bound.
    for A, n, k, m in product((-7, -2, 2, 8), range(-3, 4),
                              range(-3, 4), (-4, 0, 3)):
        T, E, D = energy(A, n, [(k, m)])
        counts['algebra'] += 1
        if T and n:
            X, Y = pell(A, k)
            # Clear negative powers directly, avoiding modular inverses.
            j = max(0, -k)
            require(((X + (n - A) * Y) * n ** j - n ** (k + j)) % abs(T) == 0,
                    'Signed Pell congruence')
            counts['signed_congruences'] += 1
    W = 258
    b = 16
    for A in (W ** W + 1, -(W ** W + 7)):
        blocks = [(-2, [(0, 1), (1, -2), (2, 4)]),
                  (-1, [(-4, 1), (-3, -1), (0, 1)]),
                  (0, [(-3, 13), (3, -9)]),
                  (1, [(-4, 1), (3, 1)]),
                  (2, [(0, 1), (1, 2), (2, 4), (3, 8)])]
        computed = [energy(A, n, rs) for n, rs in blocks]
        z = sum((Fraction(n * E, T) for (n, _), (T, E, _) in zip(blocks, computed)), Fraction(0))
        require(z.denominator == 1, 'Exact powers produce an integer aggregate')
        Omega = 1
        for T, _, _ in computed:
            require(T != 0, 'Every denominator nonzero')
            Omega *= T
        literal = sum(n * E * (Omega // T) for (n, _), (T, E, _) in zip(blocks, computed)) - z.numerator * Omega
        require(literal == 0, 'Cleared-denominator residual')
        counts['constructive_inverses'] += 1
        # Nonzero errors at zero bases remain deliberately invisible.
        blocks_changed = [(n, ([(15, -16), (-16, 15)] if n == 0 else rs)) for n, rs in blocks]
        z_changed = sum((Fraction(n * energy(A, n, rs)[1], energy(A, n, rs)[0]) for n, rs in blocks_changed), Fraction(0))
        require(z_changed == z, 'Zero block is ignored exactly')
        counts['zero_base_controls'] += 1
        # Perturb every request at every nonzero base separately.
        for j, (n, rs) in enumerate(blocks):
            if n == 0:
                continue
            for i, (k, m) in enumerate(rs):
                trial = [(nn, list(rr)) for nn, rr in blocks]
                trial[j][1][i] = (k, m + 1)
                en = [energy(A, nn, rr) for nn, rr in trial]
                rational = sum((Fraction(nn * EE, TT) for (nn, _), (TT, EE, _) in zip(trial, en)), Fraction(0))
                require(rational.denominator != 1, 'Small false power cannot pass aggregate')
                C = 1
                for nn, _ in trial:
                    if nn:
                        C *= nn ** b
                Qprime = Fraction(0)
                integer_energy = Fraction(0)
                for (nn, rr), (TT, EE, DD) in zip(trial, en):
                    if not nn:
                        continue
                    require(abs(TT) > W ** W, 'Strict modulus bound')
                    require((nn * TT > 0) == (A > 0), 'Common oriented sign')
                    dd = [C * mm - (C // (nn ** b)) * nn ** (b + kk) for kk, mm in rr]
                    Qprime += Fraction(nn * sum(d * d for d in dd), TT)
                    integer_energy += Fraction(nn * DD, TT)
                require((Qprime - C * C * integer_energy).denominator == 1,
                        'Cleared-index energies differ by an integer')
                require(0 < abs(Qprime) < 1, 'Nonzero common-sign error is shorter than one')
                counts['large_frames'] += 1
    # Verify all inequalities used by the exponent budget at the smallest b
    # and many larger values; the document contains the uniform proof.
    for b in range(16, 1001):
        W = b * b + 1
        require(68 < W and 6 * b + 2 <= W, 'Frame exponent inequality')
    print(json.dumps({'status': 'passed', 'checks': counts,
                      'scope': 'Exact finite regressions; unbounded theorem is proved in ALL_BASE_POOLING_PROOF.md'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
