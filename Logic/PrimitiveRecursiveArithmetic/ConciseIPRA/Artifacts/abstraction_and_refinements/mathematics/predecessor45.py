"""A 45-node predecessor in the raw scalar iterator language.

The mathematical proof is in predecessor45.tex. Finite evaluation is only
an implementation check. Constructors and variables each cost one node;
binder names are annotations and repeated subtrees are counted repeatedly.
"""

from functools import lru_cache
from itertools import count
import json


names = count()


def V(name):
    return ("var", name)


def Z():
    return ("zero",)


def S(t):
    return ("succ", t)


def I(n, a, body):
    name = "v" + str(next(names))
    return ("iter", n, a, name, body(V(name)))


def C(n, a, b):
    return I(n, a, lambda _: b)


def add(a, b):
    return I(b, a, S)


def clock_update(v):
    return I(S(v), v, lambda w: C(w, S(v), Z()))


def clock(n):
    return I(n, Z(), clock_update)


def ramp(n):
    return I(n, Z(), lambda u: S(C(clock(u), u, S(u))))


def factor(n):
    return I(n, n, lambda v: C(v, ramp(n), Z()))


def power2(n):
    return I(n, S(Z()), lambda u: add(u, u))


def predecessor(n):
    return I(n, Z(), lambda u: C(I(n, power2(S(u)), factor), S(u), u))


def size(t):
    match t:
        case ("var", _) | ("zero",):
            return 1
        case ("succ", a):
            return 1 + size(a)
        case ("iter", n, a, _, h):
            return 1 + size(n) + size(a) + size(h)
    raise ValueError(t)


@lru_cache(None)
def free(t):
    match t:
        case ("var", n):
            return frozenset((n,))
        case ("zero",):
            return frozenset()
        case ("succ", a):
            return free(a)
        case ("iter", n, a, x, h):
            return free(n) | free(a) | (free(h) - {x})
    raise ValueError(t)


def evaluate(t, environment):
    return _evaluate(t, tuple((x, environment[x]) for x in sorted(free(t))))


@lru_cache(None)
def _evaluate(t, values):
    env = dict(values)
    match t:
        case ("var", n):
            return env[n]
        case ("zero",):
            return 0
        case ("succ", a):
            return evaluate(a, env) + 1
        case ("iter", n, a, x, h):
            bound, state = evaluate(n, env), evaluate(a, env)
            for _ in range(bound):
                env[x] = state
                state = evaluate(h, env)
            return state
    raise ValueError(t)


def main():
    m = V("m")
    terms = {"clock_update": clock_update(m), "clock": clock(m),
             "ramp": ramp(m), "factor": factor(m), "power2": power2(m),
             "predecessor": predecessor(m)}
    counts = {k: size(t) for k, t in terms.items()}
    assert counts == {"clock_update": 9, "clock": 12, "ramp": 20,
                      "factor": 26, "power2": 9, "predecessor": 45}
    assert free(terms["predecessor"]) == {"m"}
    outputs = [evaluate(terms["predecessor"], {"m": n}) for n in range(8)]
    assert outputs == [max(n - 1, 0) for n in range(8)]
    # These are evaluations of the raw tree, without rewriting its bodies.
    result = {"node_counts": counts, "free_variables": ["m"],
              "raw_evaluation_inputs": list(range(8)),
              "raw_evaluation_outputs": outputs,
              "status": "Finite checks, not a formal universal proof",
              "raw_predecessor_ast": terms["predecessor"]}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
