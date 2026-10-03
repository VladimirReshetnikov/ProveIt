#!/usr/bin/env python3
"""Regression tests for the low-mass semilinearity proof. Standard library only, deterministic seed."""
from itertools import product
from pathlib import Path
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent
COUNTS = {}


def motion_data(alpha, displacement, pair):
    seen, types, left, right = {}, [], [], []
    a, b = pair
    l = rr = 0
    while (a, b) not in seen:
        seen[(a, b)] = len(types)
        types.append((a, b))
        left.append(l)
        right.append(rr)
        l += displacement[a]
        rr += displacement[b]
        a, b = alpha[a], alpha[b]
    mu = seen[(a, b)]
    period = len(types) - mu
    return dict(mu=mu, period=period, types=types, left=left, right=right,
                dl=l-left[mu], dr=rr-right[mu])


def affine_at(data, time):
    mu, p = data['mu'], data['period']
    if time < mu:
        return data['types'][time], data['left'][time], data['right'][time]
    k, s = divmod(time-mu, p)
    i = mu+s
    return data['types'][i], data['left'][i]+k*data['dl'], data['right'][i]+k*data['dr']


def safe_guard(data, gap, H, time):
    mu, p = data['mu'], data['period']
    c = [rr-l for rr, l in zip(data['right'], data['left'])]
    if time < mu:
        return all(gap+c[h] >= H+1 for h in range(time))
    k, s = divmod(time-mu, p)
    if not all(gap+c[h] >= H+1 for h in range(mu)):
        return False
    D = data['dr']-data['dl']
    for j in range(p):
        if j >= s and k == 0:
            continue
        last = k if j < s else k-1
        minimum = gap+c[mu+j]+(D*last if D < 0 else 0)
        if minimum < H+1:
            return False
    return True


def check_motion(alpha, displacement, pair, radius, gaps, limit=90):
    data = motion_data(alpha, displacement, pair)
    a, b = pair
    l = rr = 0
    raw = []
    for time in range(limit+1):
        assert affine_at(data, time) == ((a, b), l, rr)
        raw.append((l, rr))
        l += displacement[a]
        rr += displacement[b]
        a, b = alpha[a], alpha[b]
    checks = 0
    for gap in gaps:
        safe = True
        for time, (l, rr) in enumerate(raw):
            assert safe_guard(data, gap, 2*radius, time) == safe, (data, gap, time)
            if safe:
                assert gap+rr-l >= 1, 'An initial far flight skipped positive first entry'
            safe = safe and gap+rr-l > 2*radius
            checks += 1
    return checks


def test_guards():
    exhaustive = 0
    for radius in (0, 1, 2):
        for n in (1, 2):
            for alpha in product(range(n), repeat=n):
                for displacement in product(range(-radius, radius+1), repeat=n):
                    for pair in product(range(n), repeat=2):
                        exhaustive += check_motion(alpha, displacement, pair, radius,
                                                   range(2*radius+1, 2*radius+13), 70)
    COUNTS['exhaustive_free_prefix_guards'] = exhaustive
    rng = random.Random(20261002)
    random_checks = 0
    for _ in range(1000):
        radius, n = rng.randrange(5), rng.randrange(1, 9)
        alpha = [rng.randrange(n) for _ in range(n)]
        displacement = [rng.randrange(-radius, radius+1) for _ in range(n)]
        pair = rng.randrange(n), rng.randrange(n)
        gaps = [rng.randrange(2*radius+1, 2*radius+100) for _ in range(10)]
        random_checks += check_motion(alpha, displacement, pair, radius, gaps, 120)
    COUNTS['random_free_prefix_guards'] = random_checks
    # Large-index arithmetic checks: no linear simulation of the huge time.
    n = 10**100
    data = motion_data([0, 1], [1, -1], (0, 1))
    assert safe_guard(data, 2*n+3, 2, n)
    assert safe_guard(data, 2*n+3, 2, n+1)
    assert not safe_guard(data, 2*n+3, 2, n+2)
    assert affine_at(data, n+1)[2]-affine_at(data, n+1)[1] + 2*n+3 == 1
    COUNTS['hundred_digit_time_edges'] = 4


def comparator_residuals(L, b, s):
    return [b*(b-1), L-(2*b-1)*s-b+1]


def comparator_witness(L):
    return (1, L) if L >= 0 else (0, -L-1)


def congruence_residuals(L, d, qp, qm, a, h, b, s):
    return [qp*qm, L-d*(qp-qm)-a, a+h-(d-1), b*(b-1), a-(2*b-1)*s-b]


def congruence_witness(L, d):
    q, a = divmod(L, d)
    return (max(q, 0), max(-q, 0), a, d-1-a, int(a>0), max(a-1, 0))


def test_primitives():
    comparator_checks = 0
    for L in range(-40, 41):
        solutions = []
        for b in range(4):
            for s in range(44):
                if not any(comparator_residuals(L, b, s)):
                    solutions.append((b, s))
        assert solutions == [comparator_witness(L)]
        assert solutions[0][0] == int(L >= 0)
        comparator_checks += 1
    COUNTS['comparator_finite_domain_uniqueness'] = comparator_checks
    congruence_checks = 0
    for d in range(1, 13):
        for L in range(-60, 61):
            # Enumerate every possible bounded remainder and canonical signed
            # quotient, then all Boolean candidates; h and s follow their
            # candidate nonnegative cases. The proof supplies global bounds.
            solutions = []
            bound = abs(L)//d + 2
            for q in range(-bound, bound+1):
                qp, qm = max(q, 0), max(-q, 0)
                for a in range(d):
                    h = d-1-a
                    if L-d*q-a:
                        continue
                    for b in range(4):
                        for s in range(d+2):
                            w = (qp, qm, a, h, b, s)
                            if not any(congruence_residuals(L, d, *w)):
                                solutions.append(w)
            assert solutions == [congruence_witness(L, d)], (L, d, solutions)
            assert 1-solutions[0][-2] == int(L % d == 0)
            congruence_checks += 1
    COUNTS['signed_congruence_finite_domain_uniqueness'] = congruence_checks
    gate_checks = 0
    for u, v in product(range(2), repeat=2):
        for name, residual, expected in (
                ('AND', lambda z: z-u*v, u*v),
                ('OR', lambda z: z-u-v+u*v, int(bool(u or v))),
                ('NOT', lambda z: z-1+u, 1-u)):
            assert [z for z in range(4) if residual(z) == 0] == [expected]
            gate_checks += 1
    COUNTS['boolean_gate_truth_table_checks'] = gate_checks


def example_residuals(x, y, W):
    # ((2x-3y+1 >= 0) OR (x-y-2 ≡ 0 mod 3)) AND NOT(x+y-7 >= 0)
    b1, s1, b2, s2 = W[:4]
    qp, qm, a, h, b3, s3 = W[4:10]
    gor, gnot, gand = W[10:]
    residuals = comparator_residuals(2*x-3*y+1, b1, s1)
    residuals += comparator_residuals(x+y-7, b2, s2)
    residuals += congruence_residuals(x-y-2, 3, qp, qm, a, h, b3, s3)
    residuals += [gor-b1-(1-b3)+b1*(1-b3), gnot-1+b2, gand-gor*gnot, gand-1]
    assert len(W) == 2*2 + 6*1 + 3 == 13
    assert len(residuals) == 2*2 + 5*1 + 3 + 1 == 13
    return residuals


def test_composed_polynomial():
    checks = mutations = 0
    for x, y in product(range(16), repeat=2):
        first = comparator_witness(2*x-3*y+1)
        second = comparator_witness(x+y-7)
        congruence = congruence_witness(x-y-2, 3)
        gor = int(bool(first[0] or 1-congruence[-2]))
        gnot = 1-second[0]
        W = list(first+second+congruence+(gor, gnot, gor*gnot))
        expected = ((2*x-3*y+1 >= 0) or (x-y-2) % 3 == 0) and not x+y-7 >= 0
        P = sum(v*v for v in example_residuals(x, y, W))
        assert (P == 0) == expected
        checks += 1
        if expected:
            for index, value in enumerate(W):
                for newvalue in range(5):
                    if newvalue == value:
                        continue
                    perturbed = W.copy()
                    perturbed[index] = newvalue
                    assert sum(v*v for v in example_residuals(x, y, perturbed)) > 0
                    mutations += 1
    COUNTS['composed_polynomial_inputs'] = checks
    COUNTS['composed_polynomial_single_variable_mutations'] = mutations


def main():
    test_guards()
    test_primitives()
    test_composed_polynomial()
    receipt = {'status': 'PASS', 'seed': 20261002, 'counts': COUNTS,
               'total_checks': sum(COUNTS.values()),
               'scope': 'Proof-component arithmetic regression; not arbitrary-CA QE or formal verification',
               'sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                          for name in ('check.py',)}}
    (ROOT/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
