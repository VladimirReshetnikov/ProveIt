"""Finite source-macro diagnostics for the SR predecessor and initializer.

Place this file beside sr_evaluator.py. Every map below follows the term
definitions in sr_predecessor_and_equivalence.tex. In particular P is NOT
implemented by Python subtraction, division, or modulo. Expected numerical
values appear only in the final diagnostic comparisons.

These tests check transcription. The whole-domain proof is the written
literal-equation induction argument, not these finite runs.
"""
from functools import lru_cache
import json
from pathlib import Path

from sr_evaluator import R, T, Z, L


def successor(u):
    return u + 1


def A(a, b):
    return R(b, a, successor)


@lru_cache(None)
def cycle_map(m):
    @lru_cache(None)
    def fixed_update(u):
        return T(Z(L(u + 1, m)), u, 0)
    return fixed_update


@lru_cache(None)
def double_cycle_map(m):
    f = cycle_map(m)

    def fixed_update(u):
        return f(f(u))
    return fixed_update


def J(m, t):
    f = cycle_map(m)
    return f(R(t, m, f))


def K(m, t):
    return cycle_map(m)(R(t, m, double_cycle_map(m)))


@lru_cache(None)
def P(n):
    return K(n, n)


@lru_cache(None)
def encoded_update(h):
    def fixed_update(v):
        return successor(h(P(v)))
    return fixed_update


def initialized_iteration(n, a, h):
    return P(R(n, a, encoded_update(h)))


def zero_update(u):
    return 0


def identity_update(u):
    return u


def diagnostics(parameter_bound=7, counter_bound=12, predecessor_bound=8):
    counts = {}

    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        counts[name] = counts.get(name, 0) + 1

    for m in range(parameter_bound + 1):
        f = cycle_map(m)
        check("reset at m", f(m) == 0)
        check("transient reset at S m", f(m + 1) == 0)
        check("J initial", J(m, 0) == 0)
        check("K initial", K(m, 0) == 0)
        check("cycle diagonal", J(m, m) == m)
        check("period base", J(m, m + 1) == 0)
        for t in range(counter_bound + 1):
            check("J recurrence", J(m, t+1) == f(J(m, t)))
            check("K recurrence", K(m, t+1) == f(f(K(m, t))))
            check("bounded run", L(t,m) != 1 or J(m,t) == t)
            check("literal gate", T(L(t,m),0,J(m,t)) == T(L(t,m),0,t))
            check("full period", J(m,A(m,t)) == J(m,t))
            check("double identity", K(m,t+1) == J(m,A(t,t+1)))
            check("A commutativity", A(m,t) == A(t,m))
            check("A doubled shift", A(t+1,t+2) == A(t,t+1)+2)
    check("P initial", P(0) == 0)
    for n in range(predecessor_bound + 1):
        check("P successor", P(n+1) == n)
    for h in (zero_update, identity_update, successor):
        for a in range(3):
            check("initializer base", initialized_iteration(0,a,h) == a)
            for n in range(3):
                check("initializer step", initialized_iteration(n+1,a,h)
                      == h(initialized_iteration(n,a,h)))
    return {
        "status": "passed",
        "scope": "Finite evaluations of the source macros; no proof-assistant claim",
        "parameter_bound": parameter_bound,
        "counter_bound": counter_bound,
        "predecessor_bound": predecessor_bound,
        "checks": counts,
        "total_checks": sum(counts.values()),
        "P_values": [P(n) for n in range(predecessor_bound+2)],
        "J_values": [[J(m,t) for t in range(counter_bound+1)]
                     for m in range(parameter_bound+1)],
    }


if __name__ == "__main__":
    result = diagnostics()
    destination = Path(__file__).with_name("sr_predecessor_diagnostics.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k:v for k,v in result.items() if k != "J_values"}, indent=2))
