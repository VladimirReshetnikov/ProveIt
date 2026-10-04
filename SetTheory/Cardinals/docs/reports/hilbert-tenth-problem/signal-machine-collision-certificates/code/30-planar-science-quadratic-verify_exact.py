"""Fresh exact integer fixtures for the quadratic certificate corollary.

No upstream code is loaded or executed. This is not a universal-proof checker.
"""

import json
from fractions import Fraction


def aliases(g):
    a, b, c = g
    return 3*(a+b+c), 2*a-b-c, a+b-2*c


def forms(g):
    n, x, y = aliases(g)
    return (n+x, n-x, n+y, n-y, n-6*x-6*y), n-6*x


def certificate(g, w):
    strict, weak = forms(g)
    return sum((a-b)**2 for a, b in zip(strict, w[:5]))+(weak-w[5]+1)**2


def finite_fixtures():
    count = 0
    valid_count = 0
    for a in range(1, 10):
        for b in range(1, 10):
            for c in range(1, 10):
                g = (a, b, c)
                n, x, y = aliases(g)
                assert n > 0
                assert (Fraction(n+3*x, 9), Fraction(n-3*x+3*y, 9),
                        Fraction(n-3*y, 9)) == g
                strict, weak = forms(g)
                candidate = strict+(weak+1,)
                valid = all(t > 0 for t in strict) and weak >= 0
                assert valid == all(t > 0 for t in candidate)
                assert certificate(g, candidate) == 0
                if valid:
                    valid_count += 1
                    for i in range(6):
                        altered = list(candidate)
                        altered[i] += 1
                        assert certificate(g, altered) == 1
                assert (x*x+y*y == 0) == (a == b == c)
                count += 1
    g = (6, 1, 5)
    assert aliases(g) == (36, 6, -3)
    assert forms(g) == ((42, 30, 33, 39, 18), 0)
    assert certificate(g, (42, 30, 33, 39, 18, 1)) == 0
    assert forms((7, 1, 5)) == ((47, 31, 37, 41, 3), -9)
    return {"input_fixtures": count, "valid_half_open_inputs": valid_count,
            "retained_face_input": [6, 1, 5],
            "unique_slacks": [42, 30, 33, 39, 18, 1],
            "status": "passed",
            "scope": "Finite fixtures; uniqueness for all inputs is proved algebraically."}


if __name__ == "__main__":
    print(json.dumps(finite_fixtures(), indent=2))
