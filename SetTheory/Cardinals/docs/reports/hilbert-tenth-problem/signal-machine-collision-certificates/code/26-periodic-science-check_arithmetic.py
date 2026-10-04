#!/usr/bin/env python3
"""Newly authored exact arithmetic checks; not a signal-machine simulator.

No upstream imports, schedule loading, physical event engine, subprocesses,
network calls, or filesystem writes. It prints a JSON receipt only.
"""
import hashlib
import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def mv(a, x):
    return tuple(sum(a[i][j] * x[j] for j in range(2)) for i in range(2))


def dot(r, x):
    return sum(r[i] * x[i] for i in range(2))


def td(a):
    return a[0][0] + a[1][1], a[0][0] * a[1][1] - a[0][1] * a[1][0]


def positive_sequence(m, r, x, strict):
    """The proof's finite sign formula, evaluated with exact integers/Fractions."""
    t0, h0 = td(m)
    if t0*t0 - 4*h0 < 0:
        return (not strict) and dot(r, x) == 0 and dot(r, mv(m, x)) == 0
    bmat = mm(m, m)
    t, h = td(bmat)
    disc = t*t - 4*h
    require(t >= 0 and h >= 0 and disc >= 0, "square spectrum invariant")
    for p in (x, mv(m, x)):
        a = dot(r, p)
        b = dot(r, mv(bmat, p))
        if a < 0 or (strict and a == 0):
            return False
        if t == 0:
            if strict or b < 0:
                return False
        elif h == 0:
            if b < 0 or (strict and b == 0):
                return False
        elif disc == 0:
            if 2*b - t*a < 0:
                return False
        else:
            c = 2*b - t*a
            hh = disc*a*a - c*c
            if not (c >= 0 or (c < 0 and hh >= 0)):
                return False
    return True


def finite_terms(m, r, x, count):
    vals = []
    for unused in range(count):
        vals.append(dot(r, x))
        x = mv(m, x)
    return vals


def explicit_diagonal_test(lam, mu, coeff_a, coeff_b, strict):
    """Independent endpoint test on two explicit real exponential modes.

    Split parity but use mode coefficients, not matrix trace/discriminant.
    """
    for parity in (0, 1):
        aa = coeff_a * (lam ** parity)
        bb = coeff_b * (mu ** parity)
        la, lb = lam*lam, mu*mu
        if la < lb:
            la, lb, aa, bb = lb, la, bb, aa
        first = aa + bb
        if first < 0 or (strict and first == 0):
            return False
        if la == 0:
            if strict:
                return False
        elif la == lb:
            pass
        elif lb == 0:
            if aa < 0 or (strict and aa == 0):
                return False
        elif aa < 0:
            return False
    return True


def gadget(q, en, ez, ep, z):
    return (en*(en-1), ez*(ez-1), ep*(ep-1), en+ez+ep-1,
            q-(ep-en)*(z+1), ez*z)


def main():
    counts = {}
    # Exhaustive small rational eigenmodes under an invertible rational basis.
    # S=((1,1),(0,1)); S diag(lam,mu) S^-1=((lam,mu-lam),(0,mu)).
    diagonal_cases = 0
    roots = tuple(F(i, 2) for i in range(-4, 5))
    for lam, mu, a, b in itertools.product(roots, roots, range(-3, 4), range(-3, 4)):
        m = ((lam, mu-lam), (0, mu))
        x = (a+b, b)
        for strict in (False, True):
            actual = positive_sequence(m, (1, 0), x, strict)
            expected = explicit_diagonal_test(lam, mu, a, b, strict)
            require(actual == expected, "diagonal coefficient disagreement")
            diagonal_cases += 1
    counts['rational_diagonal_mode_comparisons'] = diagonal_cases

    # Test the closed Jordan expression directly, including lambda=0 and negative.
    jordan_cases = 0
    for lam, a, b in itertools.product(roots, range(-3, 4), range(-3, 4)):
        m = ((lam, 1), (0, lam))
        for strict in (False, True):
            actual = positive_sequence(m, (1, 0), (a, b), strict)
            if lam > 0:
                expected = (a > 0 if strict else a >= 0) and b >= 0
            elif lam < 0:
                expected = (not strict) and a == 0 and b == 0
            else:
                expected = (not strict) and a >= 0 and b >= 0
            require(actual == expected, "Jordan disagreement")
            jordan_cases += 1
    counts['jordan_and_nilpotent_comparisons'] = jordan_cases

    # Finite probes of arbitrary small integer matrices. Accepted formulas must
    # pass every inspected term; rejected formulas may fail only much later.
    # This finite probe is regression evidence, never the infinite proof.
    accepted = rejected_witnessed = rejected_unresolved = 0
    complex_cases = real_cases = 0
    rows = ((1, 0), (0, 1), (1, -1), (1, 1))
    for entries in itertools.product(range(-2, 3), repeat=4):
        m = (entries[:2], entries[2:])
        t0, h0 = td(m)
        for r in rows:
            for x in itertools.product(range(-1, 2), repeat=2):
                vals = finite_terms(m, r, x, 48)
                for strict in (False, True):
                    claim = positive_sequence(m, r, x, strict)
                    prefix = all(v > 0 if strict else v >= 0 for v in vals)
                    if claim:
                        require(prefix, "accepted formula has a bad finite term")
                        accepted += 1
                    elif prefix:
                        rejected_unresolved += 1
                    else:
                        rejected_witnessed += 1
                    if t0*t0 - 4*h0 < 0:
                        complex_cases += 1
                    else:
                        real_cases += 1
    counts['integer_matrix_48_term_probes'] = {
        'accepted': accepted, 'rejected_with_bad_term': rejected_witnessed,
        'rejected_without_bad_term_in_prefix': rejected_unresolved,
        'nonreal_spectrum_cases': complex_cases, 'real_spectrum_cases': real_cases}

    # Exhaust the sign gadget in a box sufficient for every listed Q value.
    gadget_candidates = 0
    for q in range(-16, 17):
        zeros = []
        for en, ez, ep, z in itertools.product(range(3), range(3), range(3), range(17)):
            residuals = gadget(q, en, ez, ep, z)
            gadget_candidates += 1
            if all(v == 0 for v in residuals):
                zeros.append((en, ez, ep, z))
        expected = (int(q < 0), int(q == 0), int(q > 0), max(abs(q)-1, 0))
        require(zeros == [expected], "trichotomy witness nonunique or missing")
    counts['trichotomy_assignments_checked'] = gadget_candidates
    logic_cases = 0
    for u, v in itertools.product((0, 1), repeat=2):
        for value, truth in ((u*v, u and v), (u+v-u*v, u or v), (1-u, not u)):
            require(value in (0, 1) and value == int(truth), "Boolean gate mismatch")
            logic_cases += 1
    counts['boolean_gate_cases'] = logic_cases

    # Exact rational matrix identities for the displayed four-signal example.
    # No collision engine is present: this only checks equations (9)-(11).
    m = ((F(1, 4), 0), (F(-3, 8), 1))
    clock = (F(3, 8), 0)
    guard = (F(-3, 8), 1)
    example_cases = 0
    for d, y in itertools.product(range(1, 25), range(1, 25)):
        p = (F(d), F(y))
        require(positive_sequence(m, guard, p, True) == (2*y >= d),
                "limiting boundary mismatch")
        require(positive_sequence(m, clock, p, True), "clock positivity mismatch")
        for k in range(12):
            explicit = (F(d, 4**k), F(y)-F(d, 2)*(1-F(1, 4**k)))
            require(p == explicit, "return power identity")
            p = mv(m, p)
            example_cases += 1
    counts['displayed_return_power_identities'] = example_cases

    # Check the finite-prefix threshold and its strict endpoint on exact values.
    threshold_cases = 0
    for k in range(1, 17):
        d = 2*4**k
        threshold = F(d, 2)*(1-F(1, 4**k))
        for y in (threshold-1, threshold, threshold+1):
            vals = finite_terms(m, guard, (F(d), y), k)
            require(all(v > 0 for v in vals) == (y > threshold), "strict endpoint")
            threshold_cases += 1
        late_d = 4**(k+1)
        late_y = F(late_d, 2)-1
        vals = finite_terms(m, guard, (F(late_d), late_y), k+1)
        require(all(v > 0 for v in vals[:k]) and vals[k] <= 0, "late competitor")
        threshold_cases += 1
    counts['strict_endpoint_and_late_failure_cases'] = threshold_cases

    # Rational clock summation identities, with observable cancellation of +/-1.
    clock_cases = 0
    for neutral in (F(1), F(-1), F(2)):
        for stable in (F(1, 2), F(-1, 2), F(1, 3)):
            # The positive clock sees only a positive stable mode in this test.
            if stable < 0:
                continue
            mat = ((stable, 0), (0, neutral))
            bm = mm(mat, mat)
            t, h = td(bm)
            for value in range(1, 12):
                p = (F(value), F(7))
                ae = dot((1, 0), p)
                ao = dot((1, 0), mv(mat, p))
                be = dot((1, 0), mv(bm, p))
                bo = dot((1, 0), mv(mat, mv(bm, p)))
                if 1-t+h:
                    total = (be+bo+(1-t)*(ae+ao))/(1-t+h)
                else:
                    total = (ae+ao)/(2-t)
                require(total == value/(1-stable), "observable clock sum")
                clock_cases += 1
    counts['observable_clock_sum_identities'] = clock_cases

    receipt = {'status': 'PASS', 'scope': 'new pure exact arithmetic, no physical simulation',
               'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'counts': counts,
               'limitations': ['Finite probes do not establish infinite validity.',
                               'General machine-to-macro parser/emitter is not implemented.',
                               'No upstream code or saved schedules were executed.']}
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
