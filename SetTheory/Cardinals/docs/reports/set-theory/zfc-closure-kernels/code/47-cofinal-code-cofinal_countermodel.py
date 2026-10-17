#!/usr/bin/env python3
"""Reproduce the cofinal-vacuity obstruction and arithmetic padding checks.

Only Python's standard library is required.  The all-instance theorem is
proved in cofinal_gate_analysis.md; these are finite independent diagnostics.
The model evaluates actual syntax trees, not handwritten row truth labels.
"""

from itertools import permutations, product
from math import isqrt
import json
from pathlib import Path


def imp(a, b):
    return ("imp", a, b)


def neg(a):
    return ("not", a)


def rel(i, j):
    return ("rel", i, j)


def eq(i, j):
    return ("eq", i, j)


def all_(i, a):
    return ("all", i, a)


def ex(i, a):
    return neg(all_(i, neg(a)))


TOP = ("top",)
BOT = ("bot",)


def holds(formula, assignment, hidden):
    tag, *args = formula
    if tag == "top":
        return True
    if tag == "bot":
        return False
    if tag == "rel":
        a, b = args
        return assignment[hidden] == 0 and assignment[a] != assignment[b]
    if tag == "eq":
        a, b = args
        return assignment[a] == assignment[b]
    if tag == "not":
        return not holds(args[0], assignment, hidden)
    if tag == "imp":
        return not holds(args[0], assignment, hidden) or holds(
            args[1], assignment, hidden
        )
    if tag == "all":
        i, body = args
        for value in (0, 1):
            changed = assignment[:i] + (value,) + assignment[i + 1 :]
            if not holds(body, changed, hidden):
                return False
        return True
    raise AssertionError(tag)


def vacuity(a, b, c, atom):
    return imp(atom(a, b), all_(c, atom(a, b)))


def logical_checks(hidden):
    labels = range(5)
    assignments = list(product((0, 1), repeat=5))
    formulas = [
        BOT, TOP, rel(0, 0), rel(0, 1), rel(1, 2), rel(2, 3),
        eq(0, 0), eq(0, 1), eq(1, 2), neg(rel(1, 2)),
        imp(rel(0, 1), rel(2, 3)), all_(0, rel(1, 2)),
        all_(1, rel(2, 3)), ex(2, rel(1, 2)),
    ]
    counts = {}

    def check(name, f):
        for assignment in assignments:
            assert holds(f, assignment, hidden), (name, f, assignment, hidden)
        counts[name] = counts.get(name, 0) + len(assignments)

    # rho8 is purely propositional; its 16 Boolean cases are exhaustive.
    for av, bv, cv, uv in product((False, True), repeat=4):
        truth = lambda x: TOP if x else BOT
        a, b, c, u = map(truth, (av, bv, cv, uv))
        check("rho8", imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c))))

    for a, b, c in product(labels, repeat=3):
        check("rho7", imp(eq(c, a), imp(eq(c, b), eq(a, b))))
        check("rho5", imp(eq(c, a), imp(rel(c, b), rel(a, b))))
        check("rho3", imp(eq(a, b), imp(rel(c, a), rel(c, b))))
        if c > a + b:
            check("cofinal_rel_vacuity", vacuity(a, b, c, rel))
            check("cofinal_eq_vacuity", vacuity(a, b, c, eq))

    for a, b in product(labels, repeat=2):
        check("rho1", ex(a, eq(a, b)))
        for phi in formulas:
            check("rho4", imp(all_(a, all_(b, phi)), all_(b, all_(a, phi))))

    for a in labels:
        for phi in formulas:
            check("rho6", imp(ex(a, all_(a, phi)), phi))
            for psi in formulas:
                check(
                    "rho2",
                    imp(all_(a, imp(phi, psi)), imp(all_(a, phi), all_(a, psi))),
                )

    assert all(not holds(rel(0, 0), s, hidden) for s in assignments)
    counts["uniform_F_false"] = len(assignments)

    if hidden == 0:
        f = vacuity(1, 2, 0, rel)
        witness = (0, 0, 1, 0, 0)
        changed = (1, 0, 1, 0, 0)
        atom = rel(1, 2)
        description = "R(1,2) -> forall 0 R(1,2)"
    else:
        f = vacuity(2, 3, 1, rel)
        witness = (0, 0, 0, 1, 0)
        changed = (0, 1, 0, 1, 0)
        atom = rel(2, 3)
        description = "R(2,3) -> forall 1 R(2,3)"
    assert holds(atom, witness, hidden)
    assert not holds(atom, changed, hidden)
    assert not holds(f, witness, hidden)
    return {
        "hidden_coordinate": hidden,
        "row_evaluations": counts,
        "failed_old_instance": description,
        "assignment": list(witness),
        "changed_assignment": list(changed),
    }


def pair(a, b):
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(n):
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    b = n - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def implication_code(a, b):
    return 4 * pair(a, b)


def negation_code(a):
    return implication_code(a, 1)


def pad(a):
    return negation_code(negation_code(a))


def decode(n):
    if n == 0:
        return TOP
    x, y = unpair(n // 4)
    tag = n % 4
    if tag == 0:
        return neg(decode(x)) if y == 1 else imp(decode(x), decode(y))
    if tag == 1:
        return rel(x, y)
    if tag == 2:
        return all_(x, decode(y))
    return eq(x, y)


def free(formula):
    tag, *args = formula
    if tag in ("top", "bot"):
        return set()
    if tag in ("rel", "eq"):
        return set(args)
    if tag == "not":
        return free(args[0])
    if tag == "imp":
        return free(args[0]) | free(args[1])
    if tag == "all":
        return free(args[1]) - {args[0]}
    raise AssertionError(tag)


def padding_checks():
    counter = 0
    largest_bits = 0
    for c in range(128):
        assert unpair(pair(c, c + 1)) == (c, c + 1)
        assert pad(c) > c
        assert decode(pad(c)) == neg(neg(decode(c)))
        assert free(decode(c)) == free(decode(pad(c)))
        assert c not in free(decode(c))
        if c > 0:
            assert all(i < c for i in free(decode(c)))
        for a, b in product(range(3), repeat=2):
            if c in (a, b):
                continue
            e = c
            for _ in range(a + b + 1):
                e = pad(e)
            assert e > a + b
            d = e - a - b - 1
            assert d >= 0 and a + b + d + 1 == e
            assert e not in (a, b)
            assert c not in free(decode(e))
            assert free(decode(e)) == free(decode(c))
            largest_bits = max(largest_bits, e.bit_length())
            counter += 1
    return {
        "codes": 128,
        "valid_old_triples": counter,
        "largest_padding_code_bits": largest_bits,
        "runtime_padding_required": False,
    }


def exact_gap_checks():
    bound = 10
    emitted = set()
    generated = 0
    for u, g, h in product(range(bound), repeat=3):
        x, y, z = u, u + g + 1, u + g + h + 2
        triples = list(permutations((x, y, z))) + [(x, x, y), (y, y, x)]
        for a, b, c in triples:
            assert c != a and c != b
            generated += 1
            if max(a, b, c) < bound:
                emitted.add((a, b, c))
    expected = {
        (a, b, c)
        for a, b, c in product(range(bound), repeat=3)
        if c != a and c != b
    }
    assert emitted == expected
    return {
        "parameter_bound": bound,
        "generated_triples_checked": generated,
        "distinct_permitted_triples_covered_below_bound": len(expected),
        "binary_state_cost": "unmeasured",
    }


def main():
    result = {
        "status": "finite diagnostics passed; structural proof in accompanying note",
        "logical_countermodels": [logical_checks(0), logical_checks(1)],
        "padding": padding_checks(),
        "exact_gap_enumeration": exact_gap_checks(),
        "scope": (
            "Countermodels refute unrestricted vacuity in the cofinal logical fragment. "
            "They are not models of the nonlogical set-existence theory."
        ),
    }
    target = Path(__file__).with_name("cofinal_countermodel_results.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
