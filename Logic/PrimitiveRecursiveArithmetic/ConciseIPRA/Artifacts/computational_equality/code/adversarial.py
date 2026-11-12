"""Independent adversarial regression suite for the six-rule predecessor-state kernel.

Uses only the public check function; constructors below are test data, not
copies of the checker's substitution implementation.
"""
import copy
import importlib.util
import json
import sys
from pathlib import Path

TARGET = Path(__file__).with_name("checker.py")
spec = importlib.util.spec_from_file_location("audited_kernel", TARGET)
kernel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel)

Z = ["z"]
V = lambda n: ["v", n]
S = lambda t: ["s", t]
I = lambda n, a, h: ["i", n, a, h]
E = lambda a, b: ["=", a, b]
Q = lambda a: ["q", a]
D = lambda a: ["d", a]
R = lambda a: ["refl", a]
H = lambda i: ["hyp", i]
EV = lambda p, q: ["ev", p, q]


def certificate(n, context, goal, proof):
    return {"variables": n, "context": context, "goal": goal, "proof": proof}


cases = []


def add(name, expected, c):
    cases.append((name, expected, c))


add("reflexivity at zero", True, certificate(0, [], E(Z, Z), R(Z)))
add("reflexivity of a scoped iterator", True, certificate(1, [], E(I(V(0), Z, S(V(0))), I(V(0), Z, S(V(0)))), R(I(V(0), Z, S(V(0))))))
add("common-left evaluation", True, certificate(3, [E(V(0), V(1)), E(V(0), V(2))], E(V(2), V(1)), EV(H(0), H(1))))
add("zero evaluation transports initializer", True, certificate(2, [E(V(0), V(1))], E(I(Z, V(0), S(V(0))), V(1)), EV(H(0), R(I(Z, V(0), S(V(0)))))))
add("one-step evaluation from a known state", True, certificate(2, [E(I(Z, V(0), S(V(0))), V(1))], E(I(S(Z), V(0), S(V(0))), S(V(1))), EV(H(0), R(I(S(Z), V(0), S(V(0)))))))
add("general successor evaluation", True, certificate(1, [], E(I(S(V(0)), Z, S(V(0))), S(I(V(0), Z, S(V(0))))), EV(R(I(V(0), Z, S(V(0)))), R(I(S(V(0)), Z, S(V(0)))))))
add("bound state does not capture outer variable", True, certificate(1, [], E(I(S(Z), Z, I(V(0), V(1), V(1))), I(Z, V(0), Z)), EV(EV(R(Z), R(I(Z, Z, I(V(0), V(1), V(1))))), R(I(S(Z), Z, I(V(0), V(1), V(1)))))))

# Under Q the first variable is bound. The second refers to the outer x.
qe_matrix = E(V(0), V(1))
add("QE substitutes through one binder", True, certificate(1, [Q(qe_matrix), E(Z, V(0))], E(S(V(0)), V(0)), ["qe", S(V(0)), H(0), H(1)]))
de_body = E(V(0), V(1))
add("DE permits a genuinely fresh local witness", True, certificate(1, [D(de_body)], E(V(0), V(0)), ["de", E(V(0), V(0)), H(0), R(V(1))]))
add("atomic DI progress at zero witness", True, certificate(0, [], D(E(V(0), V(0))), ["di", E(V(0), V(0)), Z, R(S(V(0)))]))
add("atomic DI cases at a nonzero witness", True, certificate(0, [], D(E(V(0), V(0))), ["di", E(V(0), V(0)), S(Z), R(S(V(0)))]))

add("reject Q as EV major", False, certificate(0, [Q(E(V(0), V(0)))], E(Z, Z), EV(H(0), R(Z))))
add("reject D as EV minor", False, certificate(0, [D(E(V(0), V(1)))], E(Z, Z), EV(R(Z), H(0))))
add("reject differing atomic left side", False, certificate(1, [], E(V(0), Z), EV(R(Z), R(V(0)))))
add("reject differing initializer", False, certificate(1, [], E(I(S(Z), V(0), V(0)), Z), EV(R(Z), R(I(S(Z), V(0), V(0))))))
add("reject neutral counter", False, certificate(1, [], E(I(V(0), Z, V(0)), Z), EV(R(Z), R(I(V(0), Z, V(0))))))
add("reject fake value shortcut at variable counter", False, certificate(1, [], E(I(S(V(0)), Z, S(V(0))), S(Z)), EV(R(I(V(0), Z, S(V(0)))), R(I(S(V(0)), Z, S(V(0)))))))
add("reject reduction of non-successor counter expression", False, certificate(0, [], E(I(I(Z, Z, V(0)), Z, V(0)), Z), EV(R(Z), R(I(I(Z, Z, V(0)), Z, V(0))))))
add("reject EV forged reversed conclusion", False, certificate(0, [], E(Z, I(Z, Z, V(0))), EV(R(Z), R(I(Z, Z, V(0))))))
add("reject QE base mismatch", False, certificate(1, [Q(qe_matrix), E(V(0), V(0))], E(S(V(0)), V(0)), ["qe", S(V(0)), H(0), H(1)]))
add("reject DE eigenvariable escaping into result", False, certificate(1, [D(de_body)], E(V(0), V(0)), ["de", E(V(0), V(0)), H(0), R(V(0))]))
add("reject DE goal with out-of-scope witness", False, certificate(0, [D(de_body)], E(V(0), V(0)), ["de", E(V(0), V(0)), H(0), R(V(0))]))
add("reject DI false atomic successor", False, certificate(0, [], D(E(V(0), Z)), ["di", E(V(0), Z), Z, H(0)]))
add("reject DI fresh eigenvariable in witness", False, certificate(0, [], D(E(V(0), V(0))), ["di", E(V(0), V(0)), V(0), R(S(V(0)))]))

add("raw successor computation keeps I0 state", True, certificate(0, [], E(I(S(Z), Z, S(V(0))), S(I(Z, Z, S(V(0))))), EV(R(I(Z, Z, S(V(0)))), R(I(S(Z), Z, S(V(0)))))))
add("successor evaluation from retained predecessor state", True, certificate(3, [E(I(V(0), V(1), S(V(0))), V(2))], E(I(S(V(0)), V(1), S(V(0))), S(V(2))), EV(H(0), R(I(S(V(0)), V(1), S(V(0)))))))
add("reject old initializer-only shortcut", False, certificate(2, [E(V(0), V(1))], E(I(S(Z), V(0), S(V(0))), S(V(1))), EV(H(0), R(I(S(Z), V(0), S(V(0)))))))
add("reject predecessor with wrong counter", False, certificate(3, [E(I(S(S(V(0))), V(1), S(V(0))), V(2))], E(I(S(V(0)), V(1), S(V(0))), S(V(2))), EV(H(0), R(I(S(V(0)), V(1), S(V(0)))))))
add("reject predecessor with wrong update body", False, certificate(3, [E(I(V(0), V(1), V(0)), V(2))], E(I(S(V(0)), V(1), S(V(0))), S(V(2))), EV(H(0), R(I(S(V(0)), V(1), S(V(0)))))))

valid = certificate(0, [], E(Z, Z), R(Z))
for name, field, value in [
    ("boolean variable count", "variables", False),
    ("negative variable count", "variables", -1),
    ("non-list context", "context", {}),
    ("fake equation tag", "goal", ["fake", Z, Z]),
    ("equation with extra field", "goal", ["=", Z, Z, Z]),
    ("unknown term constructor", "goal", E(["fake", Z, Z, Z], Z)),
    ("free variable in closed theorem", "goal", E(V(0), V(0))),
    ("out-of-scope iterator state", "proof", R(I(Z, Z, V(1)))),
    ("out-of-scope iterator counter", "proof", R(I(V(0), Z, V(0)))),
    ("boolean variable index", "proof", R(V(False))),
    ("boolean hypothesis index", "proof", H(False)),
    ("negative hypothesis index", "proof", H(-1)),
    ("unretained hypothesis", "proof", H(0)),
    ("malformed proof tag", "proof", ["unknown"]),
    ("extra reflection payload", "proof", ["refl", Z, Z]),
]:
    c = copy.deepcopy(valid)
    c[field] = value
    add("reject " + name, False, c)
c = copy.deepcopy(valid)
c["extra"] = None
add("reject extra certificate field", False, c)
c = copy.deepcopy(valid)
del c["goal"]
add("reject missing certificate field", False, c)
for c in [None, [], 0, "certificate", True]:
    add("reject nonobject certificate " + repr(c), False, c)

def run():
    results = []
    for name, expected, c in cases:
        try:
            # Round-trip test data through the actual public JSON data model.
            kernel.check(json.loads(json.dumps(c)))
            accepted = True
            detail = "accepted"
        except (ValueError, TypeError, IndexError, KeyError, RecursionError) as error:
            accepted = False
            detail = type(error).__name__
        results.append({"case": name, "expected_accept": expected, "accepted": accepted, "passed": accepted == expected, "result": detail})

    summary = {"kernel": str(TARGET), "cases": len(results), "passed": sum(r["passed"] for r in results), "failed": [r for r in results if not r["passed"]], "results": results}
    return summary


if __name__ == "__main__":
    summary = run()
    print(json.dumps(summary, indent=2))
    sys.exit(0 if not summary["failed"] else 1)
