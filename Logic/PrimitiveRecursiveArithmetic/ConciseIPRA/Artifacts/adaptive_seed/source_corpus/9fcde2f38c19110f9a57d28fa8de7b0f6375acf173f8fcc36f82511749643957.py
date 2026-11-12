"""Finite standard-model checks for the seed-shift paper.

These checks detect transcription and argument-order errors. They do not
verify a universal inference rule, a nonstandard model, or bi-interpretability.
"""
import json
from pathlib import Path


def check(condition, detail):
    if not condition:
        raise ValueError(detail)


def A(n, a):
    for _ in range(n):
        a += 1
    return a


def d(a, n):
    for _ in range(n):
        a = max(a - 1, 0)
    return a


def r(n, a):
    state = 0
    for k in range(n):
        state = state + 1 if d(a, k) == 0 else 0
    return state


def p(n, a):
    return d(n, r(n, a))


def main():
    bound = 32
    assertions = 0
    for a in range(bound + 1):
        check(p(0, a) == 0, ("base", a))
        check(p(a, a) == a, ("diagonal", a))
        assertions += 2
        for n in range(bound + 1):
            x = d(a, n)
            step = p(n, a) if x == 0 else p(n, a) + 1
            check(p(n + 1, a) == step, ("step", n, a))
            check(x == 0 or (r(n, a) == 0 and p(n, a) == n),
                  ("positive branch", n, a))
            check(A(x, p(n, a)) == a, ("reconstruction", n, a))
            check(x == 0 or A(x, n) == a,
                  ("positive reconstruction", n, a))
            assertions += 4
            for seed in (0, 1, 3, 17):
                # f(k)=A(k,seed) satisfies the tested successor recurrence.
                q = lambda k: A(d(a, k), A(p(k, a), seed))
                check(q(n + 1) == q(n), ("bridge stationarity", n, a, seed))
                check(q(a) == A(a, seed) and q(0) == A(a, seed),
                      ("bridge endpoints", a, seed))
                assertions += 2
    for a in range(bound + 1):
        for b in range(bound + 1):
            check((d(a, b) == 0 and d(b, a) == 0) == (a == b),
                  ("reflection", a, b))
            assertions += 1

    # A deliberate swapped-argument transcription fails the exact diagonal.
    wrong = d(r(1, 1), 1)
    check(wrong != 1, "The negative control unexpectedly passed")
    result = {
        "status": "passed",
        "scope": "finite standard-model calculations only",
        "bound": bound,
        "assertions": assertions,
        "negative_control": {
            "alteration": "p(n,a)=d(r(n,a),n), swapping d arguments",
            "counterexample": {"n": 1, "a": 1, "actual": wrong, "required": 1},
        },
        "universal_claims": "written proofs in seed_shift_bridge.tex",
    }
    target = Path(__file__).resolve().parents[1] / "evidence" / "seed_shift_finite_checks.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
