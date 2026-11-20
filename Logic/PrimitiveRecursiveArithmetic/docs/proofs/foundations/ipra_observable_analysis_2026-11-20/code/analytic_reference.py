#!/usr/bin/env python3
"""Exact rational examples for the analytic-algebra contracts.

The finite examples check implementations and constants. They are not
proofs of the general mathematical theorems in the report. Dependencies
are limited to the Python standard library.
"""
from fractions import Fraction as Q
from pathlib import Path
import json


def trim(p):
    p = p[:]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [Q(0)]


def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else Q(0))
                 + (q[i] if i < len(q) else Q(0)) for i in range(n)])


def pscale(p, c):
    return trim([c*x for x in p])


def psub(p, q):
    return padd(p, pscale(q, Q(-1)))


def pmul(p, q):
    result = [Q(0)] * (len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            result[i+j] += x*y
    return trim(result)


def pnorm(p):
    return sum((abs(x) for x in p), Q(0))


def coeff(p, i):
    return p[i] if i < len(p) else Q(0)


def geometric(r, count, zero, one, add, mul):
    """Sequential reference: (r**count, sum_{j<count} r**j)."""
    power, total = one, zero
    for _ in range(count):
        total = add(total, power)
        power = mul(power, r)
    return power, total


def doubling(r, rounds, one, add, mul):
    """Two multiplications per round; represents 2**rounds terms."""
    power, total = r, one
    for _ in range(rounds):
        total = add(total, mul(power, total))
        power = mul(power, power)
    return power, total


def mz(n):
    return [[Q(0) for _ in range(n)] for _ in range(n)]


def mi(n):
    a = mz(n)
    for i in range(n):
        a[i][i] = Q(1)
    return a


def madd(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mscale(a, c):
    return [[c*x for x in row] for row in a]


def msub(a, b):
    return madd(a, mscale(b, Q(-1)))


def mmul(a, b):
    n = len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(n)), Q(0))
             for j in range(n)] for i in range(n)]


def mnorm(a):
    """Exact norm induced by the l1 vector norm."""
    n = len(a)
    return max(sum((abs(a[i][j]) for i in range(n)), Q(0))
               for j in range(n))


def minverse(a):
    """Independent rational Gauss-Jordan inverse for finite examples."""
    n = len(a)
    ident = mi(n)
    rows = [a[i][:]+ident[i] for i in range(n)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        p = rows[col][col]
        rows[col] = [x/p for x in rows[col]]
        for i in range(n):
            if i != col:
                p = rows[i][col]
                rows[i] = [x-p*y for x, y in zip(rows[i], rows[col])]
    return [row[n:] for row in rows]


def matrix_polynomial(a, coefficients):
    """Horner evaluation of central rational coefficients."""
    result = mz(len(a))
    ident = mi(len(a))
    for c in reversed(coefficients):
        result = madd(mscale(ident, c), mmul(a, result))
    return result


def matrix_derivative(a, h, coefficients):
    """Insertion-position formula; no commutation of a and h."""
    n = len(a)
    powers = [mi(n)]
    for _ in range(1, len(coefficients)):
        powers.append(mmul(powers[-1], a))
    result = mz(n)
    for j in range(1, len(coefficients)):
        for i in range(j):
            term = mmul(mmul(powers[i], h), powers[j-1-i])
            result = madd(result, mscale(term, coefficients[j]))
    return result


def polynomial_checks():
    zero, one = [Q(0)], [Q(1)]
    b = [Q(0), Q(1, 4), Q(1, 8)]
    q = Q(3, 8)
    assert pnorm(b) == q
    # Independent coefficient recurrence and closed form.
    u = [Q(1), Q(1, 4)]
    for n in range(2, 66):
        u.append(u[-1]/4+u[-2]/8)
    for n, value in enumerate(u):
        assert value == Q(2, 3)*Q(1, 2)**n + Q(1, 3)*Q(-1, 4)**n
        assert value >= 0
    finite_records = []
    for count in [0, 1, 2, 3, 4, 8, 16, 32]:
        power, total = geometric(b, count, zero, one, padd, pmul)
        assert pmul(psub(one, b), total) == psub(one, power)
        assert pmul(total, psub(one, b)) == psub(one, power)
        assert all(coeff(total, j) == u[j] for j in range(count))
        assert pnorm(total) == Q(8, 5)*(1-q**count)
        _, later = geometric(b, count+3, zero, one, padd, pmul)
        assert pnorm(psub(later, total)) == Q(8, 5)*(q**count-q**(count+3))
        finite_records.append({"terms": count,
                               "residual_l1": str(pnorm(power)),
                               "partial_sum_l1": str(pnorm(total)),
                               "exact_infinite_tail_formula": str(Q(8, 5)*q**count)})
    doubling_records = []
    for rounds in range(6):
        count = 1 << rounds
        got = doubling(b, rounds, one, padd, pmul)
        expected = geometric(b, count, zero, one, padd, pmul)
        assert got == expected
        doubling_records.append({"rounds": rounds, "terms": count,
                                 "algebra_multiplications": 2*rounds,
                                 "matches_sequential": True})
    # Independent check of the coefficient-series tail formula.
    for count in range(15):
        partial = sum(u[:count], Q(0))
        coefficient_tail = Q(4, 3)*Q(1, 2)**count + Q(4, 15)*Q(-1, 4)**count
        assert partial + coefficient_tail == Q(8, 5)
        assert coefficient_tail >= 0
    schedule_records = []
    # Weaken q=3/8 to 1-1/s=1/2; s=2, H=1 in the paper.
    for k in range(8):
        count = 2*(k+2)
        tail = Q(8, 5)*q**count
        target = Q(1, 2)**(k+1)
        assert tail <= target
        schedule_records.append({"precision": k, "terms": count,
                                 "tail": str(tail), "target": str(target)})
    return {"b": [str(x) for x in b], "b_l1": str(q),
            "coefficient_recurrence_checks": len(u),
            "finite_residuals": finite_records,
            "doubling": doubling_records,
            "precision_schedule": schedule_records}


def inverse_checks():
    a = [[Q(1), Q(1, 4)], [Q(0), Q(1)]]
    b = [[Q(1), Q(0)], [Q(1, 8), Q(1)]]
    zero, one = mz(2), mi(2)
    right = msub(one, mmul(a, b))
    left = msub(one, mmul(b, a))
    assert right != left
    assert mnorm(right) == Q(1, 4)
    assert mnorm(left) == Q(9, 32)
    assert max(mnorm(left), mnorm(right)) <= Q(1, 2)
    exact = minverse(a)
    records = []
    for count in [0, 1, 2, 3, 8, 17]:
        rp, rs = geometric(right, count, zero, one, madd, mmul)
        lp, ls = geometric(left, count, zero, one, madd, mmul)
        approx = mmul(b, rs)
        assert approx == mmul(ls, b)
        assert mmul(a, approx) == msub(one, rp)
        assert mmul(approx, a) == msub(one, lp)
        actual = mnorm(msub(exact, approx))
        bound = 2*mnorm(b)*Q(1, 2)**count
        assert actual <= bound
        records.append({"terms": count, "actual_error": str(actual),
                        "certified_bound": str(bound)})
    return {"right_residual_norm": str(mnorm(right)),
            "left_residual_norm": str(mnorm(left)),
            "residuals_are_distinct": True, "cases": records}


def derivative_checks():
    zero, one = mz(2), mi(2)
    a = [[Q(0), Q(1, 4)], [Q(0), Q(0)]]
    assert mmul(a, a) == zero
    r = Q(1, 4)
    assert mnorm(a) == r
    # f_6(a) = 1+a+...+a^5, with the majorant M=R=1.
    coefficients = [Q(1)]*6
    value = matrix_polynomial(a, coefficients)
    inverse_value = minverse(msub(one, a))
    assert value == inverse_value
    records = []
    for step in [Q(1, 8), Q(1, 16), Q(1, 32), Q(1, 64)]:
        h = [[Q(0), Q(0)], [step, Q(0)]]
        assert mmul(h, h) == zero
        assert mmul(a, h) != mmul(h, a)
        derivative = matrix_derivative(a, h, coefficients)
        # Because a^2=0, the insertion series terminates and equals B h B.
        assert derivative == mmul(mmul(inverse_value, h), inverse_value)
        scalar_prime = matrix_polynomial(a, [Q(j) for j in range(1, 6)])
        naive = mmul(scalar_prime, h)
        assert derivative != naive
        perturbed = madd(a, h)
        finite_remainder = msub(msub(matrix_polynomial(perturbed, coefficients),
                                     value), derivative)
        exact_inverse = minverse(msub(one, perturbed))
        infinite_remainder = msub(msub(exact_inverse, inverse_value), derivative)
        # Independent exact resolvent expression for the inverse remainder.
        resolvent_remainder = mmul(mmul(mmul(mmul(inverse_value, h),
                                             inverse_value), h), exact_inverse)
        assert infinite_remainder == resolvent_remainder
        bound = step**2/(1-r-step)**3
        uniform_bound = step**2/(1-r-Q(1, 8))**3
        assert Q(0) < mnorm(finite_remainder) <= bound <= uniform_bound
        assert Q(0) < mnorm(infinite_remainder) <= bound
        records.append({"h_norm": str(step),
                        "h_squared_is_zero_but_remainder_nonzero": True,
                        "finite_polynomial_remainder": str(mnorm(finite_remainder)),
                        "inverse_remainder": str(mnorm(infinite_remainder)),
                        "quadratic_bound": str(bound),
                        "uniform_quadratic_bound": str(uniform_bound),
                        "naive_scalar_derivative_error": str(mnorm(msub(derivative, naive)))})
    return {"a_norm": str(r), "polynomial_coefficients": [str(x) for x in coefficients],
            "cases": records}


def main():
    result = {
        "status": "passed",
        "arithmetic": "fractions.Fraction (exact rational)",
        "scope": "selected finite implementation checks, not proofs of general theorems",
        "convolution_algebra": polynomial_checks(),
        "two_sided_inverse": inverse_checks(),
        "noncommutative_derivative": derivative_checks(),
    }
    destination = Path(__file__).resolve().parents[1] / "evidence" / "analytic_checks.json"
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "output": str(destination),
                      "coefficient_cases": 66, "doubling_cases": 6,
                      "inverse_cases": 6, "derivative_cases": 4}))


if __name__ == "__main__":
    main()
