#!/usr/bin/env python3
"""Finite controls for scalar constancy; not a proof or a proof checker.

This module has no dependency on the compact certificate checkers.  The
unbounded theorems are the mathematical arguments in the accompanying paper.
Run with Python 3.10 or later; stdout is the reproducible JSON receipt.
"""

from dataclasses import dataclass
import json


@dataclass(frozen=True)
class Point:
    level: int
    colour: int = 0


ZERO = ("0",)


def suc(t):
    return ("S", t)


def delta(s, t):
    return ("delta", s, t)


def iterator(n, a, variable, body):
    return ("I", n, a, variable, body)


def select(c, a, b):
    # All callers keep the fresh binder `v` out of b.
    return iterator(c, a, "v", b)


def evaluate(term, environment):
    """The N x {0,1,2} model; colour-zero inputs include the standard model."""
    if isinstance(term, str):
        return environment[term]
    tag = term[0]
    if tag == "0":
        return Point(0)
    if tag == "S":
        return Point(evaluate(term[1], environment).level + 1)
    if tag == "delta":
        return Point(int(evaluate(term[1], environment)
                         != evaluate(term[2], environment)))
    if tag != "I":
        raise ValueError(f"unknown term tag: {tag}")
    count = evaluate(term[1], environment).level
    state = evaluate(term[2], environment)
    for _ in range(count):
        state = evaluate(term[4], {**environment, term[3]: state})
    return state


def size(term):
    if isinstance(term, str) or term[0] == "0":
        return 1
    if term[0] == "S":
        return 1 + size(term[1])
    if term[0] == "delta":
        return 1 + size(term[1]) + size(term[2])
    return 1 + size(term[1]) + size(term[2]) + size(term[4])


def free_variables(term):
    if isinstance(term, str):
        return {term}
    if term[0] == "0":
        return set()
    if term[0] == "S":
        return free_variables(term[1])
    if term[0] == "delta":
        return free_variables(term[1]) | free_variables(term[2])
    return (free_variables(term[1]) | free_variables(term[2])
            | (free_variables(term[4]) - {term[3]}))


def swap(point, level):
    if point.level == level and point.colour:
        return Point(point.level, 3 - point.colour)
    return point


def coordinates(point):
    return [point.level, point.colour]


def main():
    # P(a) = I(a,0;u.I(delta(Su,a),u;v.Su)).  Binder names do not
    # contribute nodes.  Only the counter of the outer iterator changes
    # in the independently checked orbit O_a(n).
    update = select(delta(suc("u"), "a"), "u", suc("u"))
    predecessor = iterator("a", ZERO, "u", update)
    orbit = iterator("n", ZERO, "u", update)
    assert size(predecessor) == 11
    assert free_variables(predecessor) == {"a"}
    assert free_variables(orbit) == {"a", "n"}

    predecessor_cases = 0
    for a in range(41):
        value = evaluate(predecessor, {"a": Point(a)})
        assert value == Point(max(a - 1, 0))
        predecessor_cases += 1

    invariant_cases = 0
    for a in range(21):
        for n in range(25):
            value = evaluate(orbit, {"a": Point(a), "n": Point(n)})
            assert value == Point(n) or Point(value.level + 1) == Point(a)
            invariant_cases += 1

    cancellation_cases = 0
    for x in range(21):
        for y in range(21):
            env = {"x": Point(x), "y": Point(y)}
            assert evaluate(delta(suc("x"), suc("y")), env) == \
                evaluate(delta("x", "y"), env)
            cancellation_cases += 1

    # These bodies exercise a scalar update, a nested counter, passive
    # parameters, and one three-level nested iterator.
    bodies = [
        "u",
        suc("u"),
        delta("u", "b"),
        iterator("m", "u", "v", suc("v")),
        iterator(delta("u", "b"), "b", "v", "u"),
        iterator("u", "b", "v", delta("v", "a")),
        update,
        iterator("m", delta("u", "b"), "v",
                 iterator("v", "a", "w", suc("w"))),
    ]
    computation_cases = 0
    equivariance_cases = 0
    for n in range(5):
        for nc in range(3):
            for a in range(4):
                for ac in range(3):
                    env = {
                        "n": Point(n, nc),
                        "a": Point(a, ac),
                        "b": Point((n + a) % 4, (nc + ac) % 3),
                        "m": Point((n + 2 * a) % 3, (nc + ac + 1) % 3),
                    }
                    for body in bodies:
                        term = iterator("n", "a", "u", body)
                        value = evaluate(term, env)
                        assert evaluate(iterator(ZERO, "a", "u", body), env) \
                            == env["a"]
                        assert evaluate(iterator(suc("n"), "a", "u", body), env) \
                            == evaluate(body, {**env, "u": value})
                        computation_cases += 2
                        for level in (0, 1, 2, 3, 5):
                            moved = {name: swap(v, level) for name, v in env.items()}
                            assert evaluate(term, moved) == swap(value, level)
                            equivariance_cases += 1

    # A finite graph control for the constancy argument: every point in
    # levels 0,...,8 is linked by x--Sx to the standard zero chain.
    # One component entails constancy for any finite assignment satisfying
    # all those edge equalities.  This is not the infinite theorem.
    vertices = {Point(n, c) for n in range(9) for c in range(3)} | {Point(9)}
    parent = {v: v for v in vertices}

    def representative(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for n in range(9):
        for c in range(3):
            left, right = representative(Point(n, c)), representative(Point(n + 1))
            parent[left] = right
    components = {representative(v) for v in vertices}
    assert len(components) == 1

    x, y = Point(4, 1), Point(4, 2)
    env = {"x": x, "y": y}
    assert x != y
    assert evaluate(suc("x"), env) == evaluate(suc("y"), env)
    left = evaluate(delta(suc("x"), suc("y")), env)
    right = evaluate(delta("x", "y"), env)
    assert left == Point(0) and right == Point(1)

    # A concrete involution fixing a finite tuple of parameters.  The
    # paper's argument selects an unused level for an arbitrary finite tuple.
    parameters = [Point(0, 1), Point(4, 2), Point(6, 1), Point(0), Point(1)]
    unused_level = 3
    assert all(swap(p, unused_level) == p for p in parameters)
    moved_point = Point(unused_level, 1)
    assert swap(moved_point, unused_level) != moved_point
    assert swap(swap(moved_point, unused_level), unused_level) == moved_point

    result = {
        "scope": "Finite implementation controls, not proofs of the unbounded theorems.",
        "predecessor_expanded_nodes_with_primitive_delta": size(predecessor),
        "predecessor_free_variables": sorted(free_variables(predecessor)),
        "predecessor_standard_cases": predecessor_cases,
        "orbit_invariant_standard_cases": invariant_cases,
        "successor_comparison_standard_cases": cancellation_cases,
        "coloured_model_computation_cases": computation_cases,
        "coloured_model_equivariance_cases_including_nested_iterators": equivariance_cases,
        "finite_constancy_graph_vertices": len(vertices),
        "finite_constancy_graph_components": len(components),
        "successor_collision": [coordinates(x), coordinates(y)],
        "comparison_equation_failure_values": [coordinates(left), coordinates(right)],
        "fixed_parameter_involution_level": unused_level,
        "full_constancy_soundness_proved_by_finite_tests": False,
        "non_bi_interpretability_proved_by_finite_tests": False,
        "standalone_scalar_constancy_proof_checker_built": False,
        "compact_certificate_checkers_imported": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
