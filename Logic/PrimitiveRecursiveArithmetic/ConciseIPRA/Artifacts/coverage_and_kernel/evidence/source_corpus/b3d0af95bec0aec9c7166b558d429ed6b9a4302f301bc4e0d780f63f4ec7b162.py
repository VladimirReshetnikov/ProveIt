"""Finite arithmetic diagnostics for the tied-seed/monus presentation.

This is an evaluator and a bounded independent cross-check, not a proof
checker or a formal verification of the metatheorems. B is evaluated from
its two defining equations. P, Z, G, J, H and L are the actual displayed
macros; d is evaluated from its two proposed equations. Expected values
use ordinary Python arithmetic only on the right side of test assertions.
Run: python3 arithmetic_checks.py
"""
import json

LIMIT = 8
checks = 0


def B(n, update):
    """B_h(0)=1+h(0,0); B_h(k+1)=h(k,B_h(k))."""
    value = 1 + update(0, 0)
    for counter in range(n):
        value = update(counter, value)
    return value


def C(n, a):
    return B(n, lambda counter, state: a)


def W(n):
    return B(n, lambda counter, state: counter)


def P(n):
    return W(C(n, n))


def Z(n):
    return C(n, 0)


def G(n, a):
    return P(P(B(a, lambda counter, state: C(Z(n), state))))


def J(a, b):
    return C(Z(b), a)


def H(y, b, u):
    return J(G(y, u), G(Z(y), b))


def L(n, update):
    return B(n + 1, lambda counter, state:
             G(counter, update(P(counter), state)))


def d(x, y):
    value = x
    for _ in range(y):
        value = P(value)
    return value


def epsilon(x, y):
    return G(Z(d(x, y)), Z(d(y, x)))


def expect(left, right, label, arguments):
    global checks
    checks += 1
    if left != right:
        raise AssertionError({"label": label, "arguments": arguments,
                              "left": left, "right": right})


def first_failure(predicate, arity):
    """Return a reproducible small distinguishing input for a mutant."""
    import itertools
    for values in itertools.product(range(LIMIT + 1), repeat=arity):
        if not predicate(*values):
            return list(values)
    raise AssertionError("A proposed failure mutant was not distinguished")


def run():
    step_cases = {"zero_control": 0, "successor_control": 0}
    for n in range(LIMIT + 1):
        expect(P(n), max(n - 1, 0), "predecessor", [n])
        expect(Z(n), int(n == 0), "zero_test", [n])
        expect(G(Z(n), n), 0, "zero_reconstruction", [n])
        expect(G(Z(Z(n)), n), G(Z(Z(n)), P(n) + 1),
               "successor_reconstruction", [n])
        for a in range(LIMIT + 1):
            expect(C(n, a), a + int(n == 0), "constant_body", [n, a])
            expect(G(n, a), 0 if n == 0 else a, "gate", [n, a])
            for b in (0, 1):
                expect(J(a, b), a + b, "Boolean_increment", [a, b])
                expect(H(n, b, a), b if n == 0 else a,
                       "bounded_selector", [n, b, a])

    updates = [lambda u, v: 0, lambda u, v: u,
               lambda u, v: v + 1, lambda u, v: (u + v) % 4]
    for index, update in enumerate(updates):
        expect(L(0, update), 0, "L_base", [index])
        for n in range(LIMIT + 1):
            expect(L(n + 1, update), update(n, L(n, update)),
                   "L_step", [index, n])

    for x in range(LIMIT + 1):
        for y in range(LIMIT + 1):
            expect(d(x, y), max(x - y, 0), "monus_value", [x, y])
            expect(d(x, 0), x, "monus_base", [x])
            expect(d(x, y + 1), P(d(x, y)), "monus_step", [x, y])
            expect(d(0, y), 0, "left_zero", [y])
            expect(P(d(x + 1, y)), d(x, y), "P_commutation", [x, y])
            expect(d(x + 1, y + 1), d(x, y), "diagonal_step", [x, y])
            expect(d(x, x), 0, "diagonal_zero", [x])
            expect(d(x + 1, x), 1, "diagonal_one", [x])
            expect(G(Z(d(y, x)), d(x, d(x, y))), G(Z(d(y, x)), y),
                   "gated_complement", [x, y])
            expect(epsilon(x, y), int(x == y), "actual_equality", [x, y])

            # Independently check each intermediate step of the nontrivial
            # branch of the gated-complement successor argument.
            a = d(y + 1, x)
            if a == 0:
                step_cases["zero_control"] += 1
                expect(d(y, x), 0, "step_old_control", [x, y])
                t = d(x, y)
                expect(d(x, t), y, "step_old_complement", [x, y])
                expect(t > 0, True, "step_t_nonzero", [x, y])
                u = P(t)
                expect(t, u + 1, "step_t_coverage", [x, y])
                expect(u, d(x, y + 1), "step_u_identity", [x, y])
                v = d(x, u)
                expect(P(v), y, "step_v_predecessor", [x, y])
                expect(v > 0, True, "step_v_nonzero", [x, y])
                expect(v, y + 1, "step_target", [x, y])
            else:
                step_cases["successor_control"] += 1
                expect(G(Z(a), d(x, d(x, y + 1))), 0,
                       "step_inactive_left", [x, y])
                expect(G(Z(a), y + 1), 0, "step_inactive_right", [x, y])

    # These checks detect specific broken equations or macros. They do not
    # assert independence of the axioms or completeness of the test suite.
    mutants = {
        "monus_base_replaced_by_zero": first_failure(
            lambda x, y: G(Z(0), Z(0)) == int(x == y), 2),
        "monus_step_replaced_by_identity": first_failure(
            lambda x, y: G(Z(x), Z(y)) == int(x == y), 2),
        "monus_arguments_swapped": first_failure(
            lambda x: d(0, x) == x, 1),
        "zero_test_replaced_by_constant_zero": first_failure(
            lambda x: 0 == int(x == 0), 1),
        "gate_replaced_by_second_projection": first_failure(
            lambda x, y: Z(d(y, x)) == int(x == y), 2),
        "bounded_selector_replaced_by_gate": first_failure(
            lambda y, b, u: b not in (0, 1) or
            G(y, u) == (b if y == 0 else u), 3),
        "tied_seed_successor_removed": first_failure(
            lambda a: a == C(0, a), 1),
    }
    return {"status": "PASS", "input_bound_inclusive": LIMIT,
            "assertions": checks, "gated_successor_cases": step_cases,
            "failure_mutants_detected": len(mutants),
            "first_mutant_witnesses": mutants,
            "scope": "Finite numerical diagnostics; not formal proof verification."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
