"""Independent semantic checks of checker substitution and selected boundaries.

The bounded formula evaluator is used only to test substitution identities.
It is not claimed to be a finite model of arithmetic or of the native rules.
No production checker code is modified by this audit.
"""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("audited_checker", ROOT / "code/checker.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
rng = random.Random(839274)


def numeral(n):
    result = 0
    for _ in range(n):
        result = ["g", 0, result]
    return result


def random_term(depth, size):
    possibilities = ["zero", "parameter"] + (["variable"] if depth else [])
    if size:
        possibilities += ["gate", "iteration"]
    kind = rng.choice(possibilities)
    if kind == "zero":
        return 0
    if kind == "parameter":
        return ["p", rng.choice(["a", "b"])]
    if kind == "variable":
        return ["v", rng.randrange(depth)]
    if kind == "gate":
        return ["g", random_term(depth, size-1), random_term(depth, size-1)]
    # Bounded literal counters keep the semantic audit inexpensive while
    # the body exercises additional binders and captured outer slots.
    return ["j", numeral(rng.randrange(3)), random_term(depth+1, size-1)]


def random_formula(depth, size):
    kind = rng.randrange(3) if size else 0
    if kind == 0:
        return ["=", random_term(depth, 2), random_term(depth, 2)]
    if kind == 1:
        return ["q", random_formula(depth+1, size-1)]
    return ["d", random_formula(depth+2, size-1)]


def value(term, environment, parameters):
    if term == 0:
        return 0
    tag = term[0]
    if tag == "v":
        return environment[term[1]]
    if tag == "p":
        return parameters[term[1]]
    if tag == "g":
        control = value(term[1], environment, parameters)
        fallback = value(term[2], environment, parameters)
        return fallback+1 if control == 0 else control-1
    if tag == "j":
        counter = value(term[1], environment, parameters)
        state = 0
        for _ in range(counter):
            state = value(term[2], [state]+environment, parameters)
        return state
    raise ValueError("bad term")


def truth(formula, environment, parameters):
    tag = formula[0]
    if tag == "=":
        return value(formula[1], environment, parameters) == value(formula[2], environment, parameters)
    if tag == "q":
        return (not truth(formula[1], [0]+environment, parameters) or
                all(truth(formula[1], [y]+environment, parameters) for y in range(3)))
    if tag == "d":
        return any(not truth(formula[1], [0,x]+environment, parameters) or
                   all(truth(formula[1], [y,x]+environment, parameters) for y in range(3))
                   for x in range(3))
    raise ValueError("bad formula")


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


def main():
    counts = {"term_opening": 0, "formula_opening": 0, "term_shift": 0,
              "DE_retained_y": 0, "boundary_rejections": 0}
    scope = {"a", "b"}
    for count in (1, 2):
        for remaining in (0, 1, 2):
            for _ in range(120):
                environment = [rng.randrange(4) for _ in range(remaining)]
                parameters = {"a": rng.randrange(4), "b": rng.randrange(4)}
                images = [random_term(remaining, 2) for _ in range(count)]
                image_values = [value(t, environment, parameters) for t in images]
                t = random_term(count+remaining, 3)
                f = random_formula(count+remaining, 3)
                checker.term(t, count+remaining, scope)
                checker.formula(f, count+remaining, scope)
                opened_t = checker.replace(t, images)
                opened_f = checker.replace(f, images)
                checker.term(opened_t, remaining, scope)
                checker.formula(opened_f, remaining, scope)
                require(value(opened_t, environment, parameters) ==
                        value(t, image_values+environment, parameters), "term opening")
                counts["term_opening"] += 1
                require(truth(opened_f, environment, parameters) ==
                        truth(f, image_values+environment, parameters), "formula opening")
                counts["formula_opening"] += 1
                amount = rng.randrange(1, 4)
                original = random_term(remaining, 3)
                lifted = checker.shift(original, amount)
                checker.term(lifted, remaining+amount, scope)
                require(value(lifted, [9]*amount+environment, parameters) ==
                        value(original, environment, parameters), "term shift")
                counts["term_shift"] += 1
    for _ in range(300):
        body = random_formula(2, 3)
        checker.formula(body, 2, scope)
        opened = checker.replace(body, [["v", 0], ["p", "a"]])
        checker.formula(opened, 1, scope)
        parameters = {"a": rng.randrange(4), "b": rng.randrange(4)}
        for y in range(4):
            require(truth(opened, [y], parameters) ==
                    truth(body, [y, parameters["a"]], parameters), "DE retained y")
            counts["DE_retained_y"] += 1

    zero = ["=", 0, 0]
    one = ["g", 0, 0]
    bad_axiom = ["ax", ["=", 0, one]]
    # Failed majors cannot fall through to another proof rule.
    malformed = [
        {"goal": zero, "proof": ["tr", bad_axiom, ["=", ["v", 0], 0], bad_axiom]},
        {"goal": zero, "proof": ["qe", bad_axiom, 0, bad_axiom]},
        {"goal": zero, "proof": ["de", bad_axiom, "x", zero, ["hyp", 0]]},
        {"goal": ["=", 0, one], "proof": ["ax", ["=", 0, one]]},
        # A new eigenparameter cannot occur in its own witness.
        {"goal": ["d", zero], "proof": ["di", ["d", zero], ["p", "z"], "z", "case", ["hyp", 0]]},
        # A J state binder does not scope its counter.
        {"goal": ["=", ["j", ["v", 0], 0], 0],
         "proof": ["ax", ["=", ["j", ["v", 0], 0], 0]]},
    ]
    for packet in malformed:
        try:
            checker.verify(copy.deepcopy(packet))
        except Exception:
            counts["boundary_rejections"] += 1
        else:
            raise RuntimeError("unsound boundary packet accepted")

    result = {"status": "passed", "seed": 839274, "counts": counts,
              "checker_sha256": hashlib.sha256((ROOT / "code/checker.py").read_bytes()).hexdigest(),
              "scope": "bounded semantic substitution regression, not a soundness proof or arithmetic model"}
    (ROOT / "evidence/substitution_audit.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
