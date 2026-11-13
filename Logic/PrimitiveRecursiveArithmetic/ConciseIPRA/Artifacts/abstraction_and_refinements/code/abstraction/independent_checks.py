"""Independent symbolic and capture-avoidance tests for checker.py.

These tests inspect raw syntax and proof certificates; they do not use
finite arithmetic evaluation as a substitute for the general proof.
Run beside checker.py. Assertion checks are explicit so -O is harmless.
"""

import json
import random
import checker as k


checks = 0


def expect(condition, message):
    global checks
    if not condition:
        raise RuntimeError(message)
    checks += 1


def accepted(n, context, goal, proof):
    try:
        k.verify(n, context, goal, proof)
    except k.InvalidCertificate:
        return False
    return True


def hyp(index):
    return {"rule": "hyp", "index": index}


def reflexivity(term):
    equation = [[[], term, []], term]
    return {"rule": "brep", "equality": equation,
            "major": {"rule": "i0"}, "minor": {"rule": "i0"}}


def term_size(term):
    return 1 if type(term) is int else 1 + sum(map(term_size, term))


def formula_size(formula):
    if len(formula) == 2:
        return 1 + sum(map(term_size, formula))
    return 1 + formula_size(formula[-1])


def numeral(n):
    value = []
    for _ in range(n):
        value = [value]
    return value


def random_term(rng, slots, depth):
    atoms = [[]] + list(range(slots))
    if depth == 0 or rng.randrange(3) == 0:
        return rng.choice(atoms)
    if rng.randrange(2):
        return [random_term(rng, slots, depth - 1)]
    return [random_term(rng, slots, depth - 1),
            random_term(rng, slots, depth - 1),
            random_term(rng, slots + 1, depth - 1)]


def random_formula(rng, slots, depth):
    if depth == 0 or rng.randrange(3) == 0:
        return [random_term(rng, slots, 2), random_term(rng, slots, 2)]
    if rng.randrange(2):
        return [random_formula(rng, slots + 2, depth - 1)]
    return [0, 0, random_formula(rng, slots + 1, depth - 1)]


def main():
    # Old is the outer free parameter x. Bound u must not be replaced.
    expect(k.replace_term([0, [], [0, 1, 2]], 0, [0])
           == [[0], [], [0, [1], [2]]],
           "iterator replacement captured a bound variable")

    # Two equal-looking iterator terms differ only in whether their seed
    # names the outer parameter or the Q-bound variable.
    old = [[], 0, 0]
    formula = [0, 0, [[[], 1, 0], [[], 0, 0]]]
    abstracted = k.abstract_formula(formula, old)
    expect(abstracted == [0, 0, [1, [[], 0, 0]]],
           "AQE abstraction matched a captured occurrence")
    expect(k.substitute_formula(abstracted, old) == formula,
           "AQE capture example failed reinstantiation")

    # D binds two variables; an iterator nested inside it binds a third.
    formula = [[[0, 2, [3]], 1]]
    expect(k.abstract_formula(formula, 0) == formula,
           "wrong index under D and an iterator")
    expect(k.substitute_formula(k.abstract_formula(formula, 0), 0) == formula,
           "D/iterator reinstantiation failed")

    # All-occurrence replacement is top-down and never revisits inserts.
    expect(k.replace_term([0], 0, [0]) == [[0]],
           "inserted replacement was revisited")
    expect(k.replace_term([0], [0], []) == [],
           "replacement did not prefer the outermost match")

    # Equality bootstrap uses I0 and crossed one-endpoint BRep only.
    for term in ([], [[]], 0, [0], [0, [], [1]]):
        expect(accepted(1, [], [term, term], reflexivity(term)),
               "I0/BRep did not derive reflexivity")
    eq = [0, 1]
    symmetry = {"rule": "brep", "equality": [0, 0],
                "major": reflexivity(0), "minor": hyp(0)}
    expect(accepted(2, [eq], [1, 0], symmetry),
           "BRep symmetry bootstrap failed")

    # A positive and a capture-corrupted negative BRep certificate.
    goal = [[], [1, 0, [2]]]
    proof = {"rule": "brep", "equality": [0, 1],
             "major": hyp(0), "minor": hyp(1)}
    correct = [[0, 0, [1]], []]
    captured = [[0, 0, [0]], []]
    expect(accepted(2, [[0, 1], correct], goal, proof),
           "valid scoped BRep rejected")
    expect(not accepted(2, [[0, 1], captured], goal, proof),
           "captured BRep accepted")

    # A nontrivial compound AQE goal, with a free parameter below Q.
    goal = [0, 0, [0, 1]]
    body = k.abstract_formula(goal, 0)
    major = [0, 0, body]
    base = k.substitute_formula(body, [])
    aqe = {"rule": "aqe", "term": 0, "major": hyp(0), "base": hyp(1)}
    expect(accepted(1, [major, base], goal, aqe), "valid compound AQE rejected")
    bad_base = [0, 0, [0, 0]]
    expect(not accepted(1, [major, bad_base], goal, aqe),
           "AQE accepted a bound variable instead of zero")

    # The single introduction is progressive exactly for atomic matrices
    # with a literal-zero witness. Reflexive matrices test both branches.
    matrix = [0, 0]
    for witness in ([], [[], [], []]):
        step = [[0], [0]]
        di = {"rule": "di", "witness": witness,
              "premise": reflexivity([0])}
        expect(accepted(0, [], [matrix], di),
               "single introduction mode rejected a valid reflexive case")

    # This progress proof genuinely consumes E(z), for
    # E(y) = I(y,0;u.u)=0. It is invalid if only E(0) is supplied.
    old_value = [0, [], 0]
    new_value = [[0], [], 0]
    reverse_step = {"rule": "brep", "equality": [new_value, new_value],
                    "major": reflexivity(new_value), "minor": {"rule": "is"}}
    step_proof = {"rule": "brep", "equality": [old_value, []],
                  "major": hyp(0), "minor": reverse_step}
    matrix = [old_value, []]
    progressive = {"rule": "di", "witness": [], "premise": step_proof}
    wrong_case = {"rule": "di", "witness": [[], [], []],
                  "premise": step_proof}
    expect(accepted(0, [], [matrix], progressive),
           "a genuine induction hypothesis was not retained")
    expect(not accepted(0, [], [matrix], wrong_case),
           "case mode unsoundly retained E(z) instead of E(0)")

    # General soundness identity and marker-isolation lemma on generated
    # syntax with three kinds of binders. Each term/formula is typed first.
    rng = random.Random(20261112)
    for _ in range(300):
        slots = rng.randrange(4)
        a = random_formula(rng, slots, 3)
        t = random_term(rng, slots, 2)
        expect(k.formula_ok(a, slots) and k.term_ok(t, slots),
               "test generator produced invalid syntax")
        body = k.abstract_formula(a, t)
        expect(k.formula_ok(body, slots + 1), "abstraction broke scope")
        expect(k.substitute_formula(body, t) == a,
               "AQE abstraction/reinstantiation identity failed")

        b = random_formula(rng, slots + 1, 3)
        marker = [[], t, numeral(formula_size(b) + 1)]
        marked = k.substitute_formula(b, marker)
        expect(k.abstract_formula(marked, marker) == b,
               "oversized marker captured a fixed occurrence or missed a hole")
        expect(k.substitute_formula(k.abstract_formula(marked, marker), [])
               == k.substitute_formula(b, []),
               "marker abstraction did not preserve the zero base")

    print(json.dumps({"independent_symbolic_checks": checks,
                      "random_seed": 20261112,
                      "generated_instances": 300,
                      "status": "PASS", "scope": "finite syntax/proof regression; general proof is in the report"}, indent=2))


if __name__ == "__main__":
    main()
