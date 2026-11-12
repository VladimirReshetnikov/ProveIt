"""Finite semantic regression and exact symbolic endpoint checks.

These tests do not constitute a proof of induction, bi-interpretability,
or nonstandard correctness. The manuscript supplies those arguments.
"""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
from arithmetic import (
    ZERO, Bound, Free, Gate, Iterate, abstract, bind_iteration, bounce,
    constant_iteration, encode, evaluate, initialized, instantiate, lift,
    normalize, numeral, predecessor, replace_free, select, successor,
    validate,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def symbolic_equal(left, right, label):
    l, lc = normalize(left)
    r, rc = normalize(right)
    require(l == r, "symbolic mismatch: " + label)
    return {"name": label, "left_rewrites": lc, "right_rewrites": rc,
            "normal_form": encode(l)}


def main():
    x, a, b, v, p = map(Free, ("x", "a", "b", "v", "p"))
    symbolic = [
        symbolic_equal(predecessor(ZERO), ZERO, "P(0)=0"),
        symbolic_equal(predecessor(successor(x)), x, "P(Sx)=x"),
        symbolic_equal(select(ZERO, a, b), a, "C(0,a,b)=a"),
        symbolic_equal(select(successor(x), a, b), b, "C(Sx,a,b)=b"),
    ]

    # A passive p and a changing state v occur in the same finite update.
    update = select(v, p, successor(v))
    compiled = initialized(x, a, update, "v")
    validate(compiled)
    symbolic.append(symbolic_equal(
        initialized(ZERO, a, update, "v"), a, "compiled-I zero"))

    # The invariant base and its successor calculation under a literal
    # hypothesis V=SP(V) are represented by an arbitrary known positive
    # state S(v). The universal induction is a written proof, not this test.
    marker = Free("u")
    transition = select(marker, successor(a),
                        successor(replace_free(update, "v", predecessor(marker))))
    symbolic += [
        symbolic_equal(replace_free(transition, "u", ZERO), successor(a),
                       "load endpoint T(0)=Sa"),
        symbolic_equal(replace_free(transition, "u", successor(v)),
                       successor(update), "step endpoint T(Sv)=S(h(v))"),
        symbolic_equal(successor(predecessor(successor(a))), successor(a),
                       "encoded-state invariant base"),
        symbolic_equal(successor(predecessor(successor(update))), successor(update),
                       "encoded-state invariant successor endpoint"),
    ]

    predecessor_cases = 0
    for n in range(15):
        require(evaluate(predecessor(x), {"x": n}) == max(n-1, 0), "P value")
        predecessor_cases += 1
    selector_cases = 0
    for n in range(7):
        for av in range(6):
            for bv in range(6):
                observed = evaluate(select(x, a, b), {"x": n, "a": av, "b": bv})
                require(observed == (av if n == 0 else bv), "selector value")
                selector_cases += 1

    updates = [
        ("identity", v, lambda q, z: q),
        ("successor", successor(v), lambda q, z: q+1),
        ("predecessor", predecessor(v), lambda q, z: max(q-1, 0)),
        ("constant-passive", p, lambda q, z: z),
        ("zero-load-then-successor", update, lambda q, z: z if q == 0 else q+1),
        ("bounce", bounce(v), lambda q, z: 1 if q == 0 else q-1),
    ]
    initializer_cases = 0
    for label, body, function in updates:
        expression = initialized(x, a, body, "v")
        validate(expression)
        for n in range(5):
            for av in range(4):
                for pv in (0, 2, 5):
                    expected = av
                    for _ in range(n):
                        expected = function(expected, pv)
                    actual = evaluate(expression, {"x": n, "a": av, "p": pv})
                    require(actual == expected, "initializer value: " + label)
                    initializer_cases += 1

    # The counter remains outside its own state binder.
    same_name = bind_iteration(Free("u"), "u", successor(Free("u")))
    require(evaluate(same_name, {"u": 4}) == 4, "counter was captured")
    # An outer state used by an inner counter and update survives abstraction.
    inner = bind_iteration(Free("outer"), "inner", successor(Free("outer")))
    nested = bind_iteration(numeral(3), "outer", successor(inner))
    validate(nested)
    require(evaluate(nested) == 5, "nested state scoping")
    # Substituting an ambient Bound(0) under J must produce Bound(1).
    open_template = Iterate(ZERO, Free("slot"))
    substituted = replace_free(open_template, "slot", Bound(0))
    require(substituted == Iterate(ZERO, Bound(1)), "free substitution captured")
    require(instantiate(Iterate(ZERO, Bound(1)), Free("a")) ==
            Iterate(ZERO, Free("a")), "nested opening")
    require(instantiate(abstract(Gate(Free("slot"), Bound(0)), "slot"), Free("a")) ==
            Gate(Free("a"), Bound(0)), "abstraction/opening ambient roundtrip")
    require(lift(Iterate(Bound(0), Gate(Bound(0), Bound(1)))) ==
            Iterate(Bound(1), Gate(Bound(0), Bound(2))), "lifting nested scopes")
    # Deliberately collide with the compiler's preferred fresh marker stem.
    collision_update = Gate(Free("v"), Free("_state"))
    collision = initialized(Free("v"), Free("a"), collision_update, "v")
    validate(collision)
    require(evaluate(collision, {"v": 3, "a": 0, "_state": 7}) == 6,
            "passive marker name or external counter was captured")

    malformed = [Bound(0), Bound(-1), Bound(True), Free(""),
                 Iterate(Bound(0), ZERO), Iterate(ZERO, Bound(1)), ["0"]]
    for value in malformed:
        try:
            validate(value)
        except (ValueError, TypeError):
            pass
        else:
            raise RuntimeError("invalid term was accepted")

    result = {
        "status": "passed",
        "scope": "finite standard semantics and exact computation endpoints only",
        "predecessor_cases": predecessor_cases,
        "selector_cases": selector_cases,
        "initializer_cases": initializer_cases,
        "scoping_checks": 7,
        "malformed_terms_rejected": len(malformed),
        "symbolic_endpoint_checks": symbolic,
        "sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                   for path in (ROOT / "code/arithmetic.py", Path(__file__))},
    }
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/arithmetic_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: value for k, value in result.items()
                      if k not in ("sha256", "symbolic_endpoint_checks")}, indent=2))


if __name__ == "__main__":
    main()
