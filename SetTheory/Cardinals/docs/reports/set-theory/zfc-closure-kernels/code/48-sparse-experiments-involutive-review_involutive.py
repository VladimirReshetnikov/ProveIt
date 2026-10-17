#!/usr/bin/env python3
"""Small, independent structural controls for the involutive scheduler.

This is an audit, not a rerun of the author's numerical self-test. Its recursive
reference walk is deliberately unlike the delivered iterative threshold core.
Usage: python review_involutive.py /path/to/involutive_search.py [output.json]
"""

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys


source = Path(sys.argv[1]).resolve()
spec = importlib.util.spec_from_file_location("audited_involutive", source)
subject = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = subject
spec.loader.exec_module(subject)


def reference_word(vertex):
    word = []
    for bit in format(vertex, "b")[1:]:
        if bit == "0":
            word.append(0)
        elif word:
            word[-1] += 1
    return word


def reference_tour(depth, vertex=1):
    yield "visit", vertex
    if depth == 0:
        return
    yield "swap", 0
    yield from reference_tour(depth - 1, 2 * vertex)
    yield "swap", 0
    word = reference_word(vertex)
    forward = [] if not word else [word[-1], word[-1] + 1]
    for letter in forward:
        yield "swap", letter
    yield from reference_tour(depth - 1, 2 * vertex + 1)
    for letter in reversed(forward):
        yield "swap", letter


def reduced_action(word, letter):
    """Free product of C2 factors: only equal adjacent letters cancel."""
    if word and word[-1] == letter:
        return word[:-1]
    return word + (letter,)


def reduced_word(word):
    reduced = ()
    for letter in word:
        reduced = reduced_action(reduced, letter)
    return reduced


events = subject.universal_events()
stage_checks = []
cumulative = 0
for depth in range(7):
    bound = 1 << depth
    assert next(events) == ("stage", bound)
    actual = []
    current = ()
    while True:
        event = next(events)
        if event == ("end", bound):
            break
        kind, value = event
        assert kind in ("visit", "swap")
        actual.append(event)
        if kind == "swap":
            current = reduced_action(current, value)
        else:
            assert current == reduced_word(reference_word(value))
    expected = list(reference_tour(depth))
    assert actual == expected
    assert list(subject.stage_events(depth)) == expected
    assert current == ()
    swaps = sum(kind == "swap" for kind, _ in actual)
    assert swaps == 6 * (2**depth - 1) - 4 * depth
    assert swaps == subject.stage_length(depth)
    cumulative += swaps
    assert cumulative == 6 * 2 ** (depth + 1) - 2 * depth**2 - 8 * depth - 12
    assert cumulative == subject.cumulative_length(depth)
    stage_checks.append({"depth": depth, "events": len(actual), "swaps": swaps})

for vertex in range(1, 256):
    word = reference_word(vertex)
    assert subject.node_word(vertex) == word
    assert subject.last_letter(vertex) == (word[-1] if word else None)

word_checks = 0
for length in range(5):
    for word in itertools.product(range(4), repeat=length):
        address = subject.word_vertex(list(word))
        assert reference_word(address) == list(word)
        assert address.bit_length() - 1 == sum(letter + 1 for letter in word)
        word_checks += 1

phase_checks = 0
for left, right in itertools.product(range(3), repeat=2):
    endpoints = lambda _e, pair=(left, right): pair
    for current in range(4):
        assert subject.transpose(subject.transpose(current, (left, right)),
                                 (left, right)) == current
        for phase in (0, 1):
            state = (current, phase)
            for generator in (0, 1):
                moved = subject.lifted_step(state, generator, endpoints)
                assert subject.lifted_step(moved, generator, endpoints) == state
                phase_checks += 1
    # Both directions, both starting phases, including coincident endpoints.
    for starting_phase in (0, 1):
        state = (left, starting_phase)
        if state[1] != 0:
            state = subject.lifted_step(state, 0, endpoints)
        assert subject.lifted_step(state, 1, endpoints)[0] == right
        state = (right, starting_phase)
        if state[1] != 1:
            state = subject.lifted_step(state, 0, endpoints)
        assert subject.lifted_step(state, 1, endpoints)[0] == left

identity = lambda _e: (0, 0)
equal_start = subject.search(4, 4, 0, endpoints=identity)
assert (equal_start.status, equal_start.depth, equal_start.swaps) == ("found", 0, 0)
zero_budget = subject.search(4, 5, 0, endpoints=identity)
assert (zero_budget.status, zero_budget.current, zero_budget.swaps) == (
    "not_found_within_depth", 4, 0)
restored = subject.search(4, 5, 4, endpoints=identity)
assert restored.status == "not_found_within_depth" and restored.current == 4
one_edge = subject.search(4, 5, None, endpoints=lambda _e: (4, 5))
assert (one_edge.status, one_edge.depth, one_edge.swaps) == ("found", 1, 1)
equal_lift = subject.lifted_search(4, 4, 0)
assert (equal_lift.status, equal_lift.phase, equal_lift.swaps) == ("found", 0, 0)
zero_lift = subject.lifted_search(4, 5, 0)
assert (zero_lift.status, zero_lift.current, zero_lift.phase, zero_lift.swaps) == (
    "not_found_within_depth", 4, 0, 0)

report = {
    "review_type": "Independent mathematical/source review with small structural controls",
    "verdict": "PASS within the stated arithmetic-program scope; no binary TM state bound",
    "reviewed_files": {
        source.name: hashlib.sha256(source.read_bytes()).hexdigest(),
        source.with_name("involutive_theory.tex").name: hashlib.sha256(
            source.with_name("involutive_theory.tex").read_bytes()).hexdigest(),
    },
    "structural_controls": {
        "exact_recursive_reference_stages": stage_checks,
        "free_product_vertex_invariant_and_restoration": "all listed stages passed",
        "last_letter_vertices_checked": 255,
        "canonical_word_addresses_checked": word_checks,
        "phase_involution_controls": phase_checks,
        "edge_orientation_lifts": "both directions and phases, including equal endpoints",
        "search_boundary_controls": 6,
    },
    "mathematical_obligations": {
        "ground_completeness": "All ground contextual instances generate the ground equational congruence; each directed edge is implemented by a total endpoint transposition.",
        "word_coverage": "Canonical address 1 0 1^i1 ... 0 1^ik has depth sum(ij+1). All finite words are reached at finite stage.",
        "edge_inverse": "Right edge executes j then j+1; its return executes j+1 then j. Empty-word right edges are identities.",
        "restoration": "Vertex invariant plus return to root gives exact restoration. The same proof applies to (term,phase).",
        "call_count": "2(2^D-1) left calls plus 4(2^D-1-D) right calls gives 6(2^D-1)-4D; stated cumulative sum agrees.",
        "threshold": "For B=2^D and positive heap vertex v, v<B iff its depth is below D. At root completion B doubles and direction resets.",
        "counter_scope": "Core persistent traversal data B,v,direction; arithmetic scratch, term/phase data, and optional Python swap/report/budget metadata are additional. Vertex is unbounded path storage.",
        "initial_and_empty_words": "Initial equality test handles the root and empty proof. An edge with zero calls leaves an already-tested value unchanged.",
        "phase_lift": "F flips phase; J_e exchanges exactly (a_e,0) and (b_e,1), even when a_e=b_e. Other states are fixed. Projected orbit is exactly the ordinary orbit.",
        "phase_weight": "Generator e+1 has weight e+2; at most one weight-1 phase flip per original step yields sum(e+3).",
        "query_interface": "Explicitly conditional: an actual fixed ZFC-calibrated query and its writer/simulation remain to be emitted and proved.",
    },
    "remaining_correctness_issues_found": [],
    "limits": [
        "Ordinary mathematical/source review, not a proof-assistant kernel check.",
        "Did not rerun the author's large finite model or exhaustive involution suites.",
        "Structural controls support implementation agreement; arbitrary-depth claims use the supplied mathematical induction, not finite tests.",
        "No independent re-verification of the published first-order-to-Df3 theorem or prior E7 reduction in this controller audit.",
        "No compiled binary machine, actual ZFC query term, or state-saving claim follows from this audit.",
    ],
}
encoded = json.dumps(report, indent=2) + "\n"
if len(sys.argv) > 2:
    Path(sys.argv[2]).write_text(encoded)
else:
    print(encoded, end="")
