"""Finite primitive-recursive descriptions compiled into the 0,J grammar.

The target has exactly three AST forms:
    ('v', index), ('0',), ('J', counter, body).
The body of J binds two variables: old counter at index 0 and old register
at index 1. Existing free variables are shifted by two. There is no successor,
initializer, selector, predecessor, or ordinary recursion AST constructor.

This compiler and evaluator illustrate the written metatheorem. They are not
a derivation checker and do not provide proof-assistant verification.
"""

from __future__ import annotations

import json
from collections.abc import Sequence


Term = tuple
Program = tuple
ZERO: Term = ("0",)


def V(index: int) -> Term:
    return ("v", index)


def J(counter: Term, body: Term) -> Term:
    return ("J", counter, body)


def shift(term: Term, amount: int, depth: int = 0) -> Term:
    if term[0] == "0":
        return term
    if term[0] == "v":
        return V(term[1] + amount) if term[1] >= depth else term
    return J(shift(term[1], amount, depth), shift(term[2], amount, depth + 2))


def instantiate(term: Term, arguments: Sequence[Term], depth: int = 0) -> Term:
    if term[0] == "0":
        return term
    if term[0] == "v":
        return term if term[1] < depth else shift(arguments[term[1] - depth], depth)
    return J(
        instantiate(term[1], arguments, depth),
        instantiate(term[2], arguments, depth + 2),
    )


def well_scoped(term: Term, arity: int) -> bool:
    if not isinstance(term, (tuple, list)) or not term:
        return False
    if term[0] == "0":
        return len(term) == 1
    if term[0] == "v":
        return len(term) == 2 and type(term[1]) is int and 0 <= term[1] < arity
    return (
        term[0] == "J"
        and len(term) == 3
        and well_scoped(term[1], arity)
        and well_scoped(term[2], arity + 2)
    )


def evaluate(term: Term, environment: Sequence[int]) -> int:
    # Memoization is an evaluation optimization, not an extra AST operation.
    # A term's value depends only on its free variables; a constant J body
    # can therefore reuse its value as the old counter/register change.
    dependencies: dict[int, tuple[int, ...]] = {}
    values: dict[tuple[int, tuple[int, ...]], int] = {}

    def free(node: Term) -> tuple[int, ...]:
        identity = id(node)
        if identity not in dependencies:
            if node[0] == "0":
                result = ()
            elif node[0] == "v":
                result = (node[1],)
            else:
                result = tuple(sorted(set(free(node[1])) | {i - 2 for i in free(node[2]) if i >= 2}))
            dependencies[identity] = result
        return dependencies[identity]

    def go(node: Term, env: Sequence[int]) -> int:
        key = (id(node), tuple(env[i] for i in free(node)))
        if key in values:
            return values[key]
        if node[0] == "0":
            result = 0
        elif node[0] == "v":
            result = env[node[1]]
        else:
            counter = go(node[1], env)
            result = 1
            for i in range(counter):
                instruction = go(node[2], (i, result, *env))
                result = result + 1 if instruction == 0 else instruction - 1
        values[key] = result
        return result

    return go(term, environment)


def S(a: Term) -> Term:
    return J(a, ZERO)


ONE = S(ZERO)


def f(n: Term, a: Term) -> Term:
    return J(n, shift(a, 2))


def Z(a: Term) -> Term:
    return f(a, ONE)


def W(a: Term) -> Term:
    return f(ONE, a)


def P(a: Term) -> Term:
    return W(f(a, S(a)))


def P2(a: Term) -> Term:
    return P(P(a))


def G(c: Term, a: Term) -> Term:
    return P2(f(S(a), Z(c)))


def C(c: Term, a: Term, b: Term) -> Term:
    return P2(f(S(a), G(c, S(S(S(b))))))


def program_arity(program: Program) -> int:
    tag = program[0]
    if tag == "zero":
        assert len(program) == 2 and type(program[1]) is int and program[1] >= 0
        return program[1]
    if tag == "successor":
        assert len(program) == 1
        return 1
    if tag == "projection":
        assert len(program) == 3 and 0 <= program[2] < program[1]
        return program[1]
    if tag == "composition":
        _, arity, outer, inner = program
        assert type(arity) is int and arity >= 0
        assert program_arity(outer) == len(inner)
        assert all(program_arity(g) == arity for g in inner)
        return arity
    if tag == "recursion":
        _, initial, update = program
        arity = program_arity(initial)
        assert program_arity(update) == arity + 2
        return arity + 1
    raise ValueError(f"unknown program constructor: {tag}")


def compile_program(program: Program) -> Term:
    arity = program_arity(program)
    tag = program[0]
    if tag == "zero":
        result = ZERO
    elif tag == "successor":
        result = S(V(0))
    elif tag == "projection":
        result = V(program[2])
    elif tag == "composition":
        result = instantiate(compile_program(program[2]), [compile_program(g) for g in program[3]])
    else:
        # The output environment is (n, parameters...). Inside the J body
        # it is (i, r, n, parameters...). The old counter i is decremented
        # before supplying it to the original update, because update 0
        # installs the independent initializer.
        initial = instantiate(compile_program(program[1]), [V(k + 3) for k in range(arity - 1)])
        update = instantiate(
            compile_program(program[2]),
            [P(V(0)), V(1), *[V(k + 3) for k in range(arity - 1)]],
        )
        # C(Z(i), update, initial) has exactly the same two endpoint values
        # as C(i, initial, update). This orientation keeps the larger update
        # outside G, reducing repeated literal macro expansion.
        result = J(S(V(0)), S(C(Z(V(0)), update, initial)))
    assert well_scoped(result, arity)
    return result


def evaluate_program(program: Program, arguments: Sequence[int]) -> int:
    assert len(arguments) == program_arity(program)
    tag = program[0]
    if tag == "zero":
        return 0
    if tag == "successor":
        return arguments[0] + 1
    if tag == "projection":
        return arguments[program[2]]
    if tag == "composition":
        return evaluate_program(program[2], [evaluate_program(g, arguments) for g in program[3]])
    n, *parameters = arguments
    register = evaluate_program(program[1], parameters)
    for i in range(n):
        register = evaluate_program(program[2], (i, register, *parameters))
    return register


def nodes(term: Term) -> int:
    return 1 if term[0] != "J" else 1 + nodes(term[1]) + nodes(term[2])


SUCC: Program = ("successor",)
ADD: Program = (
    "recursion",
    ("projection", 1, 0),
    ("composition", 3, SUCC, (("projection", 3, 1),)),
)
MUL: Program = (
    "recursion",
    ("zero", 1),
    ("composition", 3, ADD, (("projection", 3, 2), ("projection", 3, 1))),
)
PRED: Program = ("recursion", ("zero", 0), ("projection", 2, 0))
FACT: Program = (
    "recursion",
    ("composition", 0, SUCC, (("zero", 0),)),
    (
        "composition",
        2,
        MUL,
        (("composition", 2, SUCC, (("projection", 2, 0),)), ("projection", 2, 1)),
    ),
)


def run_checks() -> dict[str, object]:
    rows = []
    for name, program in [("successor", SUCC), ("predecessor", PRED), ("addition", ADD), ("multiplication", MUL), ("factorial", FACT)]:
        term = compile_program(program)
        arity = program_arity(program)
        # Macro expansion is intentionally literal, so keep the nested
        # factorial term's semantic illustration small;
        # the separate macro evaluator checks factorial through argument 4.
        cases = (
            [(a,) for a in range(3 if name == "factorial" else 5)]
            if arity == 1
            else [(a, b) for a in range(3) for b in range(3)]
        )
        for arguments in cases:
            assert evaluate(term, arguments) == evaluate_program(program, arguments), (name, arguments)
        rows.append({"program": name, "arity": arity, "expanded_target_nodes": nodes(term), "cases": len(cases)})
    # A capture-avoidance regression: substituting an outer J term below
    # another J must leave each pair of local variables bound by its own J.
    template = J(S(V(0)), S(C(V(0), V(2), V(1))))
    assert well_scoped(template, 1)
    actual = P(V(0))
    substitution = instantiate(template, [actual])
    assert well_scoped(substitution, 1)
    for value in range(6):
        assert evaluate(substitution, (value,)) == evaluate(template, (evaluate(actual, (value,)),))
    return {
        "status": "passed",
        "target_constructors": ["v", "0", "J"],
        "J_local_binding_order": ["old counter", "old register"],
        "programs": rows,
        "capture_avoidance_cases": 6,
        "scope": "finite compiler/evaluator checks, not proof-assistant verification",
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
