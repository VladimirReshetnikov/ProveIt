"""Untrusted finite certificate producer and standard-model diagnostics.

Nothing in this file is imported by the standalone proof checker.
"""
import copy
import json
from pathlib import Path
import checker as K


def G(a, b):
    return ["g", a, b]


def S(a):
    return G(0, a)


def J(n, h):
    return ["j", n, h]


def E(a, b):
    return ["=", a, b]


def V(n):
    return ["v", n]


def P(name):
    return ["p", name]


def numeral(n):
    a = 0
    for _ in range(n):
        a = S(a)
    return a


def AX(a):
    return ["ax", a]


def reflexivity(t):
    r = G(S(t), 0)
    ax = AX(E(r, t))
    return ["tr", ax, E(V(0), t), ax]


def step(t):
    """Find a closed-term computational redex, never beneath a J binder.

    Returns a computation equality and a numerical context builder.
    This search is only a certificate producer; the checker rechecks
    every produced axiom and equality-transport application.
    """
    if not isinstance(t, list) or t[0] in ("v", "p"):
        return None
    tag, x, y = t
    if tag == "g" and isinstance(x, list) and x[0] == "g" and x[1] == 0:
        return E(t, x[2]), lambda hole: hole
    if tag == "j":
        if x == 0:
            return E(t, 0), lambda hole: hole
        if isinstance(x, list) and x[0] == "g" and x[1] == 0:
            return E(t, K.replace(y, [J(x[2], y)])), lambda hole: hole
    found = step(x)
    if found:
        equation, context = found
        return equation, lambda hole: [tag, context(hole), y]
    if tag == "g":
        found = step(y)
        if found:
            equation, context = found
            return equation, lambda hole: [tag, x, context(hole)]
    return None


def normalize(t, budget=1000):
    original, current = t, t
    proof = reflexivity(t)
    for count in range(budget):
        found = step(current)
        if not found:
            return current, proof, count
        equation, context = found
        assert context(equation[1]) == current
        proof = ["tr", AX(equation), E(original, context(V(0))), proof]
        current = context(equation[2])
    raise ValueError("producer normalization budget exhausted")


def initialized(counter, seed, body):
    """Untrusted general initializer compiler used to generate G/J terms."""
    state = V(0)
    next_value = K.replace(K.shift(body, 1, 1), [K.bounce(state)])
    control = K.constant_iteration(K.zero_test(state), S(S(K.shift(seed, 1))))
    return K.bounce(J(S(counter), G(control, next_value)))


def evaluate(t, parameters=None, environment=()):
    """A separate intended-model evaluator; never used to accept a proof."""
    parameters = parameters or {}
    if t == 0:
        return 0
    tag = t[0]
    if tag == "v":
        return environment[t[1]]
    if tag == "p":
        return parameters[t[1]]
    if tag == "g":
        a = evaluate(t[1], parameters, environment)
        b = evaluate(t[2], parameters, environment)
        return b + 1 if a == 0 else a - 1
    state = 0
    for _ in range(evaluate(t[1], parameters, environment)):
        state = evaluate(t[2], parameters, (state,) + environment)
    return state


def fixtures():
    cases = []

    def add(name, goal, proof, accept=True):
        cases.append({"name": name, "accept": accept,
                      "packet": {"goal": goal, "proof": proof}})

    one, two = numeral(1), numeral(2)
    wb = G(V(0), 0)
    z = P("z")
    f = J(V(0), wb)
    f0 = J(0, wb)
    recurrence = E(J(S(z), wb), G(J(z, wb), 0))
    uw_goal = E(J(two, wb), K.countdown(two, f0))
    uw_proof = ["uw", f, two, "z", AX(recurrence)]
    add("UW_on_the_primitive_bouncing_trajectory", uw_goal, uw_proof)

    # A nontrivial one-step transport inside the recurrence proof.
    outer = G(J(S(z), wb), 0)
    recurrence2 = ["tr", AX(recurrence), E(outer, G(V(0), 0)), reflexivity(outer)]
    f2 = G(J(V(0), wb), 0)
    add("UW_on_a_transported_trajectory",
        E(G(J(two, wb), 0), K.countdown(two, G(f0, 0))),
        ["uw", f2, two, "z", recurrence2])

    # UW works under a retained native formula; no induction hypothesis
    # is added by this Case-DI or by UW.
    body = E(J(V(0), wb), K.countdown(V(0), f0))
    w = P("w")
    uw_inside = ["uw", f, S(z), "w", AX(E(J(S(w), wb), G(J(w, wb), 0)))]
    add("UW_under_retained_case_context", ["d", body],
        ["di", ["d", body], 0, "z", uw_inside])

    # An actual passive numerical term occurs in f's syntax. It is
    # erased by G-computation, so its recurrence has a finite proof
    # even when the passive value is a fresh nonstandard parameter.
    passive = S(z)
    captured_f = G(S(J(V(0), wb)), passive)
    captured_left = G(S(J(S(w), wb)), passive)
    captured_right = G(G(S(J(w, wb)), passive), 0)
    left_value, left_proof, _ = normalize(captured_left)
    right_value, right_proof, _ = normalize(captured_right)
    assert left_value == right_value
    reversed_right = ["tr", right_proof, E(V(0), captured_right), reflexivity(captured_right)]
    recurrence_with_parameter = ["tr", reversed_right, E(captured_left, V(0)), left_proof]
    captured_zero = G(S(f0), V(0))
    captured_body = E(captured_zero, K.countdown(0, captured_zero))
    add("UW_with_an_actual_passive_parameter", ["d", captured_body],
        ["di", ["d", captured_body], 0, "z",
         ["uw", captured_f, 0, "w", recurrence_with_parameter]])

    # A quantified native formula remains in the retained context.
    qtruth = ["q", E(0, 0)]
    uw_quantified = ["uw", f, two, "w", AX(E(J(S(w), wb), G(J(w, wb), 0)))]
    add("UW_under_a_quantified_retained_hypothesis", ["d", qtruth],
        ["di", ["d", qtruth], 0, "z",
         ["tr", uw_quantified, qtruth, ["hyp", 0]]])

    for n in (0, 1, 2):
        a = numeral(n)
        term = K.countdown(a, S(S(a)))
        value, proof, count = normalize(term)
        assert value == two
        add(f"R2_diagonal_{n}", E(a, a), ["r2", a, a, proof])

    # The reset compiler and passive coordinates are exercised by
    # primitive-only finite derivations, not an evaluator axiom.
    compiled = initialized(two, one, S(V(0)))
    value, proof, count = normalize(compiled)
    assert value == numeral(3)
    add("compiled_initialized_successor_at_two", E(compiled, value), proof)

    # Existing logical/computation facilities.
    add("G_computation", E(G(S(two), one), two), AX(E(G(S(two), one), two)))
    add("J_zero", E(J(0, wb), 0), AX(E(J(0, wb), 0)))
    add("J_successor", E(J(one, wb), G(J(0, wb), 0)),
        AX(E(J(one, wb), G(J(0, wb), 0))))
    add("Case_DI_has_only_its_base", ["d", E(0, 0)],
        ["di", ["d", E(0, 0)], 0, "z", ["hyp", 0]])
    di = ["di", ["d", E(0, 0)], 0, "z", ["hyp", 0]]
    closure = ["de", di, "a", ["q", E(0, 0)], ["hyp", 0]]
    add("DE_and_QE", E(0, 0), ["qe", closure, two, reflexivity(0)])

    # The older equation-induction instruction is deliberately rejected.
    add("reject_old_step_mode", ["d", E(0, 0)],
        ["di", ["d", E(0, 0)], 0, "z", "step", ["hyp", 0]], False)
    add("reject_UW_wrong_recurrence", uw_goal,
        ["uw", f, two, "z", reflexivity(J(S(z), wb))], False)
    add("reject_UW_escaping_parameter", uw_goal,
        ["uw", f, P("z"), "z", AX(recurrence)], False)
    add("reject_UW_open_template", uw_goal,
        ["uw", J(V(1), wb), two, "z", AX(recurrence)], False)
    add("reject_UW_template_free_fresh_name", uw_goal,
        ["uw", P("z"), two, "z", AX(recurrence)], False)
    add("reject_UW_reused_active_parameter", ["d", body],
        ["di", ["d", body], 0, "z",
         ["uw", f, S(z), "z", AX(recurrence)]], False)
    bad = copy.deepcopy(uw_proof)
    bad[-1] = ["hyp", 0]
    add("reject_UW_missing_premise", uw_goal, bad, False)

    # Dropping one successor from R2 would be unsound: L(0,2)=2
    # would incorrectly imply 1=0. The real rule requires L(0,3)=2.
    value, zero_two_proof, count = normalize(K.countdown(0, two))
    assert value == two
    add("reject_R2_wrong_start_offset", E(one, 0),
        ["r2", one, 0, zero_two_proof], False)
    add("reject_R2_wrong_observation", E(0, 0),
        ["r2", 0, 0, reflexivity(one)], False)
    add("reject_R2_unscoped_argument", E(0, 0),
        ["r2", P("a"), 0, zero_two_proof], False)
    add("reject_escaped_DE_parameter", E(0, 0),
        ["de", di, "a", E(P("a"), P("a")), reflexivity(P("a"))], False)
    add("reject_boolean_zero", E(False, 0), AX(E(False, 0)), False)
    add("reject_float_zero", E(0.0, 0), AX(E(0.0, 0)), False)
    add("reject_free_goal", E(P("a"), P("a")), reflexivity(P("a")), False)
    add("reject_open_goal", E(V(0), V(0)), reflexivity(V(0)), False)
    add("reject_false_G_equation", E(G(0, one), 0), AX(E(G(0, one), 0)), False)
    add("reject_unknown_axiom", E(0, one), ["oracle", E(0, one)], False)
    return cases


if __name__ == "__main__":
    destination = Path(__file__).with_name("fixtures.json")
    cases = fixtures()
    destination.write_text(json.dumps({"cases": cases}, indent=2) + "\n")
    print(f"Wrote {len(cases)} finite fixtures to {destination}")
