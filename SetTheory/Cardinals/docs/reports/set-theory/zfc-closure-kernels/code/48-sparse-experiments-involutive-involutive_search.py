#!/usr/bin/env python3
"""Reset-free, inside-out ground-equational search: an executable specification.

This is a new scheduling/representation experiment, NOT a binary Turing machine
and NOT an expanded Con(ZFC) instance. The E7 mathematical basis and arithmetic
term codec are attributed to ProveIt intake 154/source 38 (2026-10-16). The
ordinary contextual-walk completeness argument predates this experiment.

New here: an unoriented equality instance acts as a total endpoint transposition;
a binary word-tree traversal restores its input without storing/copying that
input; and inside-out contexts require no reversal of a list of frames.

Each stage is finite. Running all stages without a depth limit halts exactly on
E7-provable ground equalities, subject to the mathematical ideal of unbounded
integer storage. Python exceptions, memory exhaustion and interruption are not
successful refutations. The traversal index is unbounded path storage: this is
not a constant-space claim, a physical reversibility claim, or a state bound.
"""

from __future__ import annotations

import argparse
import functools
import itertools
import json
from dataclasses import asdict, dataclass
from math import isqrt
from pathlib import Path
from typing import Callable, Iterator


Pattern = str | tuple


def n(a: Pattern, b: Pattern) -> Pattern:
    return ("n", a, b)


def q(a: Pattern) -> Pattern:
    return ("q", a)


def r(a: Pattern) -> Pattern:
    return ("r", a)


def neg(a: Pattern) -> Pattern:
    return n(a, a)


def join(a: Pattern, b: Pattern) -> Pattern:
    return n(neg(a), neg(b))


x, y, z = "x", "y", "z"
# These are mathematical identities from the attributed E7 source, not a new
# axiom minimization. The ground leaf c does NOT occur in any of the seven rows.
BASIS = (
    ("Sh1", n(n(x, n(n(y, x), x)), n(y, n(z, x))), y),
    ("Rhom", r(n(x, y)), n(r(x), r(y))),
    ("R3", r(r(r(x))), x),
    ("Qext", join(x, q(x)), q(x)),
    ("Qadd", q(join(x, y)), join(q(x), q(y))),
    ("Qcomp", q(neg(q(x))), neg(q(x))),
    ("Qrot", q(r(q(r(r(x))))), r(q(r(r(q(x)))))),
)


def natural(value: int) -> int:
    if type(value) is not int or value < 0:
        raise ValueError("Expected a natural number")
    return value


def pair(a: int, b: int) -> int:
    natural(a)
    natural(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(value: int) -> tuple[int, int]:
    natural(value)
    diagonal = (isqrt(8 * value + 1) - 1) // 2
    b = value - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def q_code(a: int) -> int:
    return 3 * a + 1


def r_code(a: int) -> int:
    return 3 * a + 2


def n_code(a: int, b: int) -> int:
    return 3 * pair(a, b) + 3


def instance(pattern: Pattern, values: tuple[int, int, int]) -> int:
    """Only the seven fixed, finite templates are interpreted here.

    Ground term operands are integers already; they are never parsed or matched.
    The recursion depth is bounded by the depth of the fixed template.
    """
    if isinstance(pattern, str):
        return values[{"x": 0, "y": 1, "z": 2}[pattern]]
    op = pattern[0]
    a = instance(pattern[1], values)
    if op == "q":
        return q_code(a)
    if op == "r":
        return r_code(a)
    return n_code(a, instance(pattern[2], values))


def context_encode(frames: list[tuple[int, int]]) -> int:
    """Frames are ordered from the hole toward the root, not in prefix order.

    Tags 0/1 mean q/r (the sibling is ignored); 2 means n(hole,sibling),
    3 means n(sibling,hole). Retaining ignored siblings makes the numerical
    encode/decode round trip exact, even for noncanonical unary frames.
    """
    value = 0
    for tag, sibling in reversed(frames):
        if type(tag) is not int or not 0 <= tag < 4:
            raise ValueError("Invalid context tag")
        value = 1 + 4 * pair(natural(sibling), value) + tag
    return value


def context_decode(value: int) -> Iterator[tuple[int, int]]:
    natural(value)
    while value:
        body, tag = divmod(value - 1, 4)
        sibling, tail = unpair(body)
        assert tail < value
        yield tag, sibling
        value = tail


def context_endpoints(value: int, left: int, right: int) -> tuple[int, int]:
    """Apply the same context in one forward pass, without a frame stack."""
    for tag, sibling in context_decode(value):
        if tag == 0:
            left, right = q_code(left), q_code(right)
        elif tag == 1:
            left, right = r_code(left), r_code(right)
        elif tag == 2:
            left, right = n_code(left, sibling), n_code(right, sibling)
        else:
            left, right = n_code(sibling, left), n_code(sibling, right)
    return left, right


@dataclass(frozen=True)
class Edge:
    axiom: int
    context: int
    substitutions: tuple[int, int, int]


def edge_encode(edge: Edge) -> int:
    if type(edge.axiom) is not int or not 0 <= edge.axiom < len(BASIS):
        raise ValueError("Axiom index is outside the fixed basis")
    if len(edge.substitutions) != 3:
        raise ValueError("An E7 substitution has three entries")
    a, b, c = edge.substitutions
    return len(BASIS) * pair(edge.context, pair(a, pair(b, c))) + edge.axiom


def edge_decode(value: int) -> Edge:
    body, axiom = divmod(natural(value), len(BASIS))
    context, body = unpair(body)
    a, body = unpair(body)
    b, c = unpair(body)
    return Edge(axiom, context, (a, b, c))


def edge_endpoints(value: int) -> tuple[int, int]:
    edge = edge_decode(value)
    _, left, right = BASIS[edge.axiom]
    return context_endpoints(
        edge.context,
        instance(left, edge.substitutions),
        instance(right, edge.substitutions),
    )


def transpose(current: int, endpoints: tuple[int, int]) -> int:
    """A total involution; equal endpoints make the operation the identity."""
    left, right = endpoints
    if current == left:
        return right
    if current == right:
        return left
    return current


def lifted_step(
    state: tuple[int, int],
    generator: int,
    endpoints: Callable[[int], tuple[int, int]] = edge_endpoints,
) -> tuple[int, int]:
    """Optional lift with one selected endpoint comparison per equality move.

    Generator 0 flips the bit. Generator e+1 matches the left endpoint in phase
    0 and the right endpoint in phase 1; a successful match replaces the term
    and flips phase. Every operation is an involution. The phase costs storage
    or control states; this function is not evidence that the lift saves states.
    """
    current, phase = state
    if phase not in (0, 1):
        raise ValueError("The phase must be a bit")
    natural(generator)
    if generator == 0:
        return current, 1 - phase
    left, right = endpoints(generator - 1)
    expected, replacement = (left, right) if phase == 0 else (right, left)
    if current == expected:
        return replacement, 1 - phase
    return state


def last_letter(vertex: int) -> int | None:
    """Last generator in the vertex word, or None for an empty word.

    Delete the leading 1 from the binary vertex address. Each 0 begins a
    generator, and following 1s increment that generator. Leading 1s before the
    first 0 are ignored. Hence the last letter is the trailing-one count unless
    the entire vertex address consists of 1s.
    """
    if type(vertex) is not int or vertex < 1:
        raise ValueError("A binary-tree vertex is a positive integer")
    value, result = vertex, 0
    while value & 1:
        value >>= 1
        result += 1
    return None if value == 0 else result


def node_word(vertex: int) -> list[int]:
    """Inspection helper; the actual scheduler never constructs this list."""
    if type(vertex) is not int or vertex < 1:
        raise ValueError("A binary-tree vertex is a positive integer")
    word: list[int] = []
    for bit in bin(vertex)[3:]:
        if bit == "0":
            word.append(0)
        elif word:
            word[-1] += 1
    return word


def word_vertex(word: list[int]) -> int:
    """Canonical address 1 0 1^j1 0 1^j2 ...; used only for proof/tests."""
    vertex = 1
    for letter in word:
        natural(letter)
        vertex <<= 1
        vertex = (vertex << letter) | ((1 << letter) - 1)
    return vertex


def universal_events() -> Iterator[tuple[str, int]]:
    """Successive iterative tours, represented by a binary-leaf threshold.

    A ('swap', j) event applies the j-th involution. A ('visit', v) event is
    optional inspection metadata. ('stage', B) and ('end', B) mark the start
    and end of the tour whose leaves are numbered B through 2*B-1, B=2**D.
    Persistent traversal data are B, the vertex integer, and a direction bit;
    temporary arithmetic data include parent, branch and last letter. In
    particular, no vertex-depth counter is needed: v < B means internal node.
    The vertex stores path history. There is no recursion or reverse list.
    """
    bound, vertex, descending = 1, 1, True
    yield "stage", bound
    yield "visit", vertex
    while True:
        if descending and vertex < bound:
            # Appending 0 appends generator 0 to the represented word.
            yield "swap", 0
            vertex *= 2
            yield "visit", vertex
            continue
        if vertex == 1:
            yield "end", bound
            bound *= 2
            descending = True
            yield "stage", bound
            yield "visit", vertex
            continue
        parent, branch = divmod(vertex, 2)
        if branch == 0:
            # Return from the left child, then enter the right child.
            yield "swap", 0
            letter = last_letter(parent)
            if letter is not None:
                yield "swap", letter
                yield "swap", letter + 1
            vertex = 2 * parent + 1
            descending = True
            yield "visit", vertex
        else:
            # The reverse of [letter, letter+1] is [letter+1, letter].
            letter = last_letter(parent)
            if letter is not None:
                yield "swap", letter + 1
                yield "swap", letter
            vertex = parent
            descending = False


def stage_events(depth: int) -> Iterator[tuple[str, int]]:
    """Finite stage view for inspection/tests, not a second search controller.

    Earlier tours are generated and discarded, without executing their swaps.
    Search consumes universal_events directly and does not repeat this prefix.
    """
    natural(depth)
    requested_bound = 1 << depth
    active = False
    for kind, value in universal_events():
        if kind == "stage":
            active = value == requested_bound
        elif kind == "end":
            if active:
                return
        elif active:
            yield kind, value


def stage_generators(depth: int) -> Iterator[int]:
    for kind, value in stage_events(depth):
        if kind == "swap":
            yield value


def stage_length(depth: int) -> int:
    natural(depth)
    return 6 * ((1 << depth) - 1) - 4 * depth


def cumulative_length(depth: int) -> int:
    natural(depth)
    return 6 * (1 << (depth + 1)) - 2 * depth * depth - 8 * depth - 12


@dataclass(frozen=True)
class SearchResult:
    status: str
    depth: int
    swaps: int
    current: int
    last_generator: int | None


@dataclass(frozen=True)
class LiftedSearchResult:
    status: str
    depth: int
    swaps: int
    current: int
    phase: int
    last_generator: int | None


def search(
    current: int,
    target: int,
    max_depth: int | None = None,
    endpoints: Callable[[int], tuple[int, int]] = edge_endpoints,
) -> SearchResult:
    """No source/root term is retained after initialization.

    max_depth=None is the ideal semidecision procedure. A bounded negative
    result only reports exhaustion of the chosen finite depth budget.
    """
    natural(current)
    natural(target)
    if max_depth is not None:
        natural(max_depth)
    if current == target:
        return SearchResult("found", 0, 0, current, None)
    swaps, stage_bound = 0, 1
    budget_bound = None if max_depth is None else 1 << max_depth
    for kind, value in universal_events():
        if kind == "stage":
            stage_bound = value
        elif kind == "swap":
            current = transpose(current, endpoints(value))
            swaps += 1
            if current == target:
                return SearchResult("found", stage_bound.bit_length() - 1,
                                    swaps, current, value)
        elif kind == "end" and budget_bound is not None and value >= budget_bound:
            return SearchResult("not_found_within_depth", value.bit_length() - 1,
                                swaps, current, None)
    raise AssertionError("Unreachable")


def lifted_search(current: int, target: int, max_depth: int) -> LiftedSearchResult:
    natural(current)
    natural(target)
    natural(max_depth)
    if current == target:
        return LiftedSearchResult("found", 0, 0, current, 0, None)
    state, swaps, stage_bound = (current, 0), 0, 1
    del current  # The changing pair is the sole retained source-term value.
    budget_bound = 1 << max_depth
    for kind, value in universal_events():
        if kind == "stage":
            stage_bound = value
        elif kind == "swap":
            state = lifted_step(state, value)
            swaps += 1
            if state[0] == target:
                return LiftedSearchResult("found", stage_bound.bit_length() - 1,
                                          swaps, *state, value)
        elif kind == "end" and value >= budget_bound:
            return LiftedSearchResult("not_found_within_depth", max_depth,
                                      swaps, *state, None)
    raise AssertionError("Unreachable")


def all_involutions(size: int) -> list[tuple[int, ...]]:
    """Exhaustive finite test oracle, not part of the proposed search engine."""
    result = []
    values = [-1] * size

    def visit() -> None:
        try:
            point = values.index(-1)
        except ValueError:
            result.append(tuple(values))
            return
        values[point] = point
        visit()
        values[point] = -1
        for partner in range(point + 1, size):
            if values[partner] != -1:
                continue
            values[point], values[partner] = partner, point
            visit()
            values[point] = values[partner] = -1

    visit()
    return result


def evaluate_pattern(pattern: Pattern, values: tuple[int, int, int]) -> int:
    """Eight-element test algebra: NAND, q=id, r rotates three atoms."""
    if isinstance(pattern, str):
        return values[{"x": 0, "y": 1, "z": 2}[pattern]]
    op = pattern[0]
    left = evaluate_pattern(pattern[1], values)
    if op == "q":
        return left
    if op == "r":
        return ((left << 1) & 7) | (left >> 2)
    return 7 ^ (left & evaluate_pattern(pattern[2], values))


@functools.lru_cache(maxsize=None)
def evaluate_code(code: int, constant: int) -> int:
    if code == 0:
        return constant
    body, tag = divmod(code - 1, 3)
    if tag == 0:
        return evaluate_code(body, constant)
    if tag == 1:
        value = evaluate_code(body, constant)
        return ((value << 1) & 7) | (value >> 2)
    left, right = unpair(body)
    return 7 ^ (evaluate_code(left, constant) & evaluate_code(right, constant))


def self_test() -> dict:
    if not __debug__:
        raise RuntimeError("Run the tests without Python optimization")
    counts: dict[str, int] = {}
    for value in range(5000):
        assert pair(*unpair(value)) == value
        assert context_encode(list(context_decode(value))) == value
        assert edge_encode(edge_decode(value)) == value
    counts["pair_context_edge_round_trips_each"] = 5000
    for a in range(32):
        for b in range(32):
            assert unpair(pair(a, b)) == (a, b)
    counts["coordinate_round_trips"] = 1024

    # Independent order check: inside-out r then q means q(r(c)).
    assert context_endpoints(context_encode([(1, 0), (0, 0)]), 0, 1) == (
        q_code(r_code(0)), q_code(r_code(1)))
    assert n_code(0, n_code(0, 0)) == 30
    counts["inside_out_and_top_controls"] = 2

    for depth in range(10):
        reduced: list[int] = []
        visited = []
        number = 0
        for kind, value in stage_events(depth):
            if kind == "swap":
                number += 1
                if reduced and reduced[-1] == value:
                    reduced.pop()
                else:
                    reduced.append(value)
            else:
                visited.append(value)
                expected: list[int] = []
                for letter in node_word(value):
                    if expected and expected[-1] == letter:
                        expected.pop()
                    else:
                        expected.append(letter)
                assert reduced == expected
        assert reduced == []
        assert sorted(visited) == list(range(1, 1 << (depth + 1)))
        assert number == stage_length(depth)
        assert sum(stage_length(d) for d in range(depth + 1)) == cumulative_length(depth)
    counts["complete_free_involution_tree_stages"] = 10
    counts["free_involution_vertex_invariants"] = sum((1 << (d + 1)) - 1 for d in range(10))

    weighted_words = 0
    for length in range(5):
        for word_tuple in itertools.product(range(4), repeat=length):
            word = list(word_tuple)
            vertex = word_vertex(word)
            assert node_word(vertex) == word
            assert vertex.bit_length() - 1 == sum(letter + 1 for letter in word)
            weighted_words += 1
    counts["canonical_weighted_word_addresses"] = weighted_words

    finite_cases = finite_swaps = 0
    for size in range(1, 5):
        for generators in itertools.product(all_involutions(size), repeat=2):
            for source in range(size):
                component = {source}
                changed = True
                while changed:
                    larger = component | {g[v] for g in generators for v in component}
                    changed = larger != component
                    component = larger
                current, visited = source, {source}
                for generator in stage_generators(2 * (size - 1)):
                    # The tour includes larger letters. Interpreting those as
                    # identity embeds this two-generator action in N generators.
                    if generator < 2:
                        current = generators[generator][current]
                    visited.add(current)
                    finite_swaps += 1
                assert current == source
                assert visited == component
                finite_cases += 1
    counts["exhaustive_finite_involution_actions"] = finite_cases
    counts["finite_action_swaps"] = finite_swaps

    evaluations = 0
    for values in itertools.product(range(8), repeat=3):
        for _, left, right in BASIS:
            assert evaluate_pattern(left, values) == evaluate_pattern(right, values)
            evaluations += 1
    counts["complete_eight_element_basis_evaluations"] = evaluations
    transpositions = semantic_checks = lifted_checks = 0
    for generator in range(1000):
        endpoints = edge_endpoints(generator)
        for current in (0, 1, 2, 17, *endpoints):
            assert transpose(transpose(current, endpoints), endpoints) == current
            transpositions += 1
            for phase in (0, 1):
                state = (current, phase)
                assert lifted_step(lifted_step(state, generator + 1), generator + 1) == state
                assert lifted_step(lifted_step(state, 0), 0) == state
                lifted_checks += 1
        for constant in range(8):
            assert evaluate_code(endpoints[0], constant) == evaluate_code(endpoints[1], constant)
            semantic_checks += 1
    counts["ground_edge_involution_checks"] = transpositions
    counts["ground_edge_semantic_checks"] = semantic_checks
    counts["lifted_involution_checks_including_flip"] = lifted_checks

    positive_queries = []
    lifted_positive_queries = []
    for generator, (name, _, _) in enumerate(BASIS):
        left, right = edge_endpoints(generator)
        result = search(left, right, max_depth=generator + 1)
        assert result.status == "found"
        positive_queries.append({"axiom": name, **asdict(result)})
        lifted = lifted_search(left, right, max_depth=generator + 3)
        assert lifted.status == "found"
        lifted_positive_queries.append({"axiom": name, **asdict(lifted)})
    negative = search(0, r_code(0), max_depth=8)
    assert negative.status == "not_found_within_depth"
    assert evaluate_code(0, 1) == 1 and evaluate_code(r_code(0), 1) == 2
    assert negative.current == 0
    counts["complete_positive_basis_searches"] = len(positive_queries)
    counts["model_separated_bounded_searches"] = 1
    # Source and target are separated by the same fully checked finite model.
    lifted_negative = lifted_search(0, r_code(0), max_depth=8)
    assert lifted_negative.status == "not_found_within_depth"
    assert (lifted_negative.current, lifted_negative.phase) == (0, 0)
    # Both directions work from either phase after at most one preparation flip.
    for generator in range(32):
        left, right = edge_endpoints(generator)
        for phase in (0, 1):
            forward = (left, phase)
            if phase != 0:
                forward = lifted_step(forward, 0)
            assert lifted_step(forward, generator + 1)[0] == right
            backward = (right, phase)
            if phase != 1:
                backward = lifted_step(backward, 0)
            assert lifted_step(backward, generator + 1)[0] == left
    counts["lifted_bidirectional_edge_controls"] = 128
    counts["complete_lifted_positive_basis_searches"] = len(lifted_positive_queries)

    # Merely repeating a fair list of distinct endpoint swaps need not visit
    # the whole connected component. This six-edge K4 example repeats at 0.
    cycle_edges = [(0, 1), (0, 3), (1, 2), (1, 3), (0, 2), (2, 3)]
    current, visited = 0, {0}
    for _ in range(10):
        for endpoints in cycle_edges:
            current = transpose(current, endpoints)
            visited.add(current)
    assert current == 0 and visited == {0, 1, 2}
    # Noncommuting moves must be undone in reverse order.
    a, b = (0, 1), (1, 2)
    forward = transpose(transpose(0, a), b)
    correct_return = transpose(transpose(forward, b), a)
    wrong_return = transpose(transpose(forward, a), b)
    assert correct_return == 0 and wrong_return != 0
    counts["scheduler_negative_controls"] = 2
    return {
        "scope": "Original reset-free scheduler and inside-out numerical edge reference; no compiled TM or ZFC payload",
        "prior_basis": "ProveIt intake 154/source 38; arithmetic codec and seven identities attributed",
        "new_features": [
            "unoriented endpoint involutions",
            "binary weighted-word traversal with B,v,direction threshold control",
            "inside-out streaming contexts",
            "optional one-comparison phase lift",
        ],
        "counts": counts,
        "positive_queries": positive_queries,
        "lifted_positive_queries": lifted_positive_queries,
        "negative_query": {**asdict(negative), "separating_model_c": 1, "source_value": 1, "target_value": 2},
        "lifted_negative_query": asdict(lifted_negative),
        "periodic_fair_list_counterexample": {"edges": cycle_edges, "root": 0, "visited": sorted(visited), "missed": 3},
        "stage_lengths": [{"depth": d, "swaps": stage_length(d), "cumulative": cumulative_length(d)} for d in range(10)],
        "limits": [
            "Only finite executions were tested; the unbounded correctness claim rests on the accompanying mathematical proof.",
            "No literal binary table, E7-to-ZFC target, query writer, PA proof artifact or Lean/Coq theorem was produced.",
            "The vertex integer encodes unbounded path history; no constant-space or physical reversibility claim is made.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    test = commands.add_parser("self-test")
    test.add_argument("--output", type=Path)
    run = commands.add_parser("search")
    run.add_argument("source", type=int)
    run.add_argument("target", type=int)
    run.add_argument("--max-depth", type=int, required=True)
    args = parser.parse_args()
    if args.command == "self-test":
        result = self_test()
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps(asdict(search(args.source, args.target, args.max_depth)), indent=2))


if __name__ == "__main__":
    main()
