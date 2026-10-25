#!/usr/bin/env python3
"""Independent finite checks for the reciprocal-pooling arithmetic lemma.

Uses only Python's standard library. Checks exact sparse-polynomial identities,
signed Pell congruences, and some full-hypothesis examples. These checks do not
prove the universally quantified size estimate or the inherited ZFC calibration;
the accompanying independent mathematical review supplies the arithmetic proof.
"""
from fractions import Fraction
from math import gcd, isqrt
import json
import sys


class CheckFailure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


# Sparse polynomials in named commuting indeterminates. Monomials are sorted
# tuples of names. This checker imports no producer or inherited source module.
def constant(c):
    return {(): c} if c else {}


def variable(name):
    return {(name,): 1}


def add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            result[monomial] = result.get(monomial, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def scale(polynomial, factor):
    return {m: c * factor for m, c in polynomial.items() if c * factor}


def multiply(left, right):
    result = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            monomial = tuple(sorted(lm + rm))
            result[monomial] = result.get(monomial, 0) + lc * rc
    return {m: c for m, c in result.items() if c}


def square(polynomial):
    return multiply(polynomial, polynomial)


def check_symbolic_identities():
    checks = 0
    for count in (1, 2):
        A, n = variable("A"), variable("n")
        T = add(scale(multiply(A, n), 2), scale(square(n), -1), constant(-1))
        H, S, sum_y2, sum_delta2, z_defects = {}, {}, {}, {}, {}
        for index in range(count):
            m, X, Y, Z = (variable(f"{name}{index}") for name in ("m", "X", "Y", "Z"))
            m_minus_X = add(m, scale(X, -1))
            D = add(m_minus_X, Z)
            delta = add(D, scale(multiply(n, Y), -1))
            H = add(H, multiply(Y, m_minus_X))
            S = add(S, square(D), scale(square(Y), -1))
            sum_y2 = add(sum_y2, square(Y))
            sum_delta2 = add(sum_delta2, square(delta))
            z_defects = add(z_defects, multiply(Y, add(Z, scale(multiply(A, Y), -1))))
        E = add(S, scale(multiply(n, H), -2))
        # This is an identity even before imposing any Z_i=A*Y_i row.
        defect = add(E, scale(multiply(T, sum_y2), -1), scale(sum_delta2, -1),
                     scale(multiply(n, z_defects), -2))
        require(not defect, f"free-Z square identity failed for {count} requests")
        checks += 1
        K, L = variable("K"), variable("L")
        first = add(K, scale(H, -2), scale(multiply(add(scale(A, 2), scale(n, -1)), L), -1))
        second = add(S, scale(multiply(n, K), -1), L)
        elimination = add(E, scale(multiply(T, L), -1), scale(second, -1),
                          scale(multiply(n, first), -1))
        require(not elimination, f"old-pool elimination identity failed for {count} requests")
        checks += 1
        # A sign error in the constant term of T must be detected.
        wrong_T = add(T, constant(2))
        wrong_defect = add(E, scale(multiply(wrong_T, sum_y2), -1),
                           scale(sum_delta2, -1), scale(multiply(n, z_defects), -2))
        require(bool(wrong_defect), "corrupted modulus escaped the symbolic check")
        checks += 1
    # Abstract two-block recombination identity, independent of local formulas.
    E0, E1, T0, T1, L0, L1, z = (variable(name) for name in ("E0", "E1", "T0", "T1", "L0", "L1", "z"))
    output = add(multiply(E0, T1), multiply(E1, T0), scale(multiply(z, multiply(T0, T1)), -1))
    reconstruction = add(
        multiply(T1, add(E0, scale(multiply(T0, L0), -1))),
        multiply(T0, add(E1, scale(multiply(T1, L1), -1))),
        multiply(add(L0, L1, scale(z, -1)), multiply(T0, T1)),
    )
    require(not add(output, scale(reconstruction, -1)), "two-block recombination failed")
    return checks + 1


def pell_pair(A, index):
    """Coordinates of (A+sqrt(A^2-1))^index, with conjugation for index<0."""
    X, Y = 1, 0
    for _ in range(abs(index)):
        X, Y = A * X + (A * A - 1) * Y, X + A * Y
    return X, -Y if index < 0 else Y


def exact_integer_power(base, exponent):
    value = Fraction(base) ** exponent
    require(value.denominator == 1, "example requests a nonintegral power")
    return value.numerator


def check_small_pell_congruences():
    count = 0
    negative_indices = 0
    for A in (-5, -3, -2, 2, 3, 5):
        for base in (-3, -2, -1, 1, 2, 3):
            T = 2 * A * base - base * base - 1
            require(T != 0, "unexpected zero modulus in test family")
            require(gcd(base, T) == 1, "own-base invertibility failed")
            for index in range(-5, 6):
                X, Y = pell_pair(A, index)
                require(X * X - (A * A - 1) * Y * Y == 1, "Pell norm failed")
                image = X + (base - A) * Y
                if index < 0:
                    difference = base ** (-index) * image - 1
                    negative_indices += 1
                else:
                    difference = image - base ** index
                require(difference % T == 0, "signed Pell congruence failed")
                # Independently check the free-coordinate arithmetic identity.
                for m in (-2, 0, 3):
                    Z = A * Y
                    delta = m - X + Z - base * Y
                    E = (m - X + Z) ** 2 - Y * Y - 2 * base * Y * (m - X)
                    require(delta * delta == E - T * Y * Y, "numeric square identity failed")
                count += 1
    return count, negative_indices


def block(A, base, requests):
    T = 2 * A * base - base * base - 1
    H = S = y2 = delta2 = 0
    for index, m in requests:
        X, Y = pell_pair(A, index)
        Z = A * Y
        D = m - X + Z
        H += Y * (m - X)
        S += D * D - Y * Y
        y2 += Y * Y
        delta2 += (D - base * Y) ** 2
    E = S - 2 * base * H
    require(delta2 == E - T * y2, "block square identity failed")
    return T, H, S, E, delta2


def check_full_hypothesis_examples():
    W = 258
    b = isqrt(W - 1)
    A_magnitude = W ** W + 1
    valid = invalid = 0
    for sign in (-1, 1):
        A = sign * A_magnitude
        for q in (-3, -2, 1, 2):
            bases = (q, q + 1)
            requests = []
            for base in bases:
                indices = (-2, 3) if abs(base) == 1 else (1, 2)
                req = [(k, exact_integer_power(base, k)) for k in indices]
                require(base * base < W and all(k*k < W and m*m < W for k,m in req),
                        "example outside square frame")
                requests.append(req)
            blocks = [block(A, n, req) for n, req in zip(bases, requests)]
            require(blocks[0][0] * blocks[1][0] > 0, "modulus orientation failed")
            require(min(abs(row[0]) for row in blocks) > W**W, "modulus lower bound failed")
            quotient = sum((Fraction(row[3], row[0]) for row in blocks), Fraction())
            require(quotient.denominator == 1, "true powers failed pooled integrality")
            z = quotient.numerator
            T0, T1 = blocks[0][0], blocks[1][0]
            E0, E1 = blocks[0][3], blocks[1][3]
            require(E0*T1 + E1*T0-z*T0*T1 == 0, "true powers failed polynomial residual")
            for base, row in zip(bases, blocks):
                T, H, S, E, delta2 = row
                require(E % T == 0, "individual divisibility not restored")
                L = E // T
                K = 2*H+(2*A-base)*L
                require(K-2*H-(2*A-base)*L == 0 and S-base*K+L == 0,
                        "old private witness restoration failed")
            valid += 1
            # Perturb one genuine output while keeping every square-frame bound.
            bad_requests = [list(req) for req in requests]
            k, m = bad_requests[0][0]
            bad_requests[0][0] = (k, m+1)
            require((m+1)**2 < W, "negative control outside square frame")
            bad_blocks = [block(A, n, req) for n, req in zip(bases, bad_requests)]
            bad_sum = sum((Fraction(row[3], row[0]) for row in bad_blocks), Fraction())
            require(bad_sum.denominator != 1, "false power unexpectedly passed full-hypothesis pooling")
            C = (bases[0]*bases[1])**b
            rational_errors = Fraction()
            total_error = 0
            for base, req, row in zip(bases, bad_requests, bad_blocks):
                for index, output in req:
                    d = C*output-(C//(base**b))*base**(b+index)
                    total_error += d*d
                    rational_errors += Fraction(d*d, row[0])
            require(0 < abs(rational_errors) < 1, "cleared error not strictly between zero and one")
            require((C*C*bad_sum-rational_errors).denominator == 1,
                    "clearing changed rational sum by a noninteger")
            require(total_error < W**W, "finite example violated proved error budget")
            invalid += 1
    return valid, invalid


def check_assumption_counterexamples():
    require(Fraction(1, 2)+Fraction(1, -2) == 0,
            "opposite-sign cancellation counterexample failed")
    require(Fraction(1, 2)+Fraction(1, 2) == 1,
            "missing-strict-bound counterexample failed")
    return 2


def main():
    symbolic = check_symbolic_identities()
    congruences, signed = check_small_pell_congruences()
    valid, invalid = check_full_hypothesis_examples()
    assumption_controls = check_assumption_counterexamples()
    receipt = {
        "status": "PASS",
        "symbolic_identity_and_corruption_checks": symbolic,
        "small_pell_congruence_cases": congruences,
        "negative_index_congruence_cases": signed,
        "full_hypothesis_true_power_examples": valid,
        "full_hypothesis_perturbed_output_controls": invalid,
        "hypothesis_necessity_counterexamples": assumption_controls,
        "scope": "Finite independent arithmetic checks only; unbounded theorem is proved in the accompanying review.",
        "proof_assistant_certificate": False,
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (CheckFailure, ValueError, ZeroDivisionError) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}), file=sys.stderr)
        raise SystemExit(1)
