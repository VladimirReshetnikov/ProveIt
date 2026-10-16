#!/usr/bin/env python3
"""Finite compiler/coding/transition checks; no consistency or infinite-run claim."""
from __future__ import annotations
import itertools
import json
import random
from pathlib import Path

from build_carrier import Terms, interpreter, compile_machine, parse_tm


def native_step(transitions, config):
    q, left, bit, right = config
    if (q, bit) not in transitions:
        return None
    write, direction, nxt = transitions[q, bit]
    if direction == "R":
        return (nxt, [write]+left, right[0] if right else 0, right[1:])
    return (nxt, left[1:], left[0] if left else 0, [write]+right)


def decode_bool(t, term):
    zero, one = t.var("observe_zero"), t.var("observe_one")
    head, args, steps = t.view(t.app(term, zero, one))
    assert not args and head in (zero, one), (head, args)
    return int(head == one)


def decode_list(t, term, limit=10000):
    cons, nil = t.var("observe_cons"), t.var("observe_nil")
    result = []
    for _ in range(limit):
        head, args, _ = t.view(t.app(term, cons, nil))
        if head == nil:
            assert not args
            return result
        assert head == cons and len(args) == 2
        result.append(decode_bool(t, args[0]))
        term = args[1]
    raise AssertionError("List bound exhausted")


def decode_config(t, term):
    observer = t.var("observe_config")
    head, args, steps = t.view(t.app(term, observer))
    if head == t.K:
        assert args == [observer]
        return None, steps
    assert head == observer and len(args) == 4, (head, args)
    path = decode_list(t, args[0])
    q = 0
    for bit in path:
        q = 2*q + bit
    return (q, decode_list(t, args[1]), decode_bool(t, args[2]),
            decode_list(t, args[3])), steps


def sk_step(t, core, machine, config):
    q, left, bit, right = config
    inputs = (machine["states"][q],
              t.list([t.boolean(x) for x in left]),
              t.boolean(bit), t.list([t.boolean(x) for x in right]))
    # F is the same compiled term used under Y in the actual payload.
    result = t.app(core["F"], machine["table"], core["config"], *inputs)
    return decode_config(t, result)


def parse_tree_bits(bits):
    """Independent pure-tree parser for o=0, application=1."""
    frames, result = [], None
    for ch in bits:
        if result is not None:
            raise ValueError("Trailing tree data")
        if ch == "1":
            frames.append(None)
            continue
        if ch != "0":
            raise ValueError("Bad tree bit")
        node = "o"
        while frames and frames[-1] is not None:
            node = (frames.pop(), node)
        if frames:
            frames[-1] = node
        else:
            result = node
    if frames or result is None:
        raise ValueError("Truncated tree")
    return result


def decode_carrier_tree(tree):
    """Decode the one-constant image iteratively, rejecting non-image trees."""
    k, s = ("o", "o"), ("o", ("o", "o"))
    todo, output = [tree], []
    while todo:
        current = todo.pop()
        if current == k:
            output.append("00")
        elif current == s:
            output.append("01")
        elif isinstance(current, tuple) and current[0] != "o":
            output.append("1")
            todo.append(current[1])
            todo.append(current[0])
        else:
            raise ValueError("Not the image of an SK term")
    return "".join(output)


def full_tree_reducts(tree, one_constant=False):
    """All ONE-step tree reducts, including every context (test-only).

    This evaluator deliberately uses literal nested tuples, independently of
    the production compiler's hash-consed graph and left-spine evaluator.
    """
    if not isinstance(tree, tuple):
        return set()
    k = ("o", "o") if one_constant else "K"
    s = ("o", ("o", "o")) if one_constant else "S"
    answer = set()
    left, right = tree
    if isinstance(left, tuple) and left[0] == k:
        answer.add(left[1])
    if (isinstance(left, tuple) and isinstance(left[0], tuple)
            and left[0][0] == s):
        first, second, third = left[0][1], left[1], right
        answer.add(((first, third), (second, third)))
    answer.update((child, right) for child in full_tree_reducts(left, one_constant))
    answer.update((left, child) for child in full_tree_reducts(right, one_constant))
    return answer


def one_encode(tree):
    if tree == "K":
        return ("o", "o")
    if tree == "S":
        return ("o", ("o", "o"))
    return one_encode(tree[0]), one_encode(tree[1])


def small_terms(max_leaves):
    exact = {1: {"K", "S"}}
    for n in range(2, max_leaves+1):
        exact[n] = {(left, right)
                    for i in range(1, n)
                    for left in exact[i] for right in exact[n-i]}
    return set().union(*exact.values())


def main():
    rng = random.Random(20261016)
    statistics = {}

    # Guard the exact-output issue: basic abstraction is not eta abstraction.
    t = Terms()
    naively_compiled_K = t.compile(t.lam("x y", t.var("x")))
    assert naively_compiled_K != t.K
    p, q = t.var("p"), t.var("q")
    head, args, _ = t.view(t.app(naively_compiled_K, p, q))
    assert head == p and args == []
    statistics["eta_distinction_regression"] = "passed"

    # Full terminating executions for 100 acyclic random machines plus empty.
    successful, total_reductions = 0, 0
    for case in range(101):
        n = 0 if case == 0 else rng.randrange(1, 7)
        transitions = {(state, bit): (rng.randrange(2), rng.choice(("L", "R")),
                                     rng.randrange(state+1, n+1))
                       for state in range(n) for bit in (0, 1)}
        t = Terms()
        core = interpreter(t)
        machine = compile_machine(t, core, 0, transitions)
        native = (0, [], 0, [])
        while native is not None:
            native = native_step(transitions, native)
        head, args, steps = t.view(machine["P"], fuel=100000)
        assert head == t.K and args == [], (case, head, args)
        total_reductions += steps
        successful += 1
    statistics["complete_halting_machine_runs"] = successful
    statistics["halting_run_SK_contractions"] = total_reductions

    # Check every combination of movement/write/scan and empty/nonempty sides.
    local_cases = 0
    for write, direction, bit, left, right in itertools.product(
            (0, 1), ("L", "R"), (0, 1), ([], [0], [1, 0]), ([], [1], [0, 1])):
        transitions = {(0, bit): (write, direction, 1)}
        t = Terms()
        core = interpreter(t)
        machine = compile_machine(t, core, 0, transitions)
        native = (0, left, bit, right)
        got, _ = sk_step(t, core, machine, native)
        assert got == native_step(transitions, native)
        # The target state has no transition and must yield literal K.
        halted, _ = sk_step(t, core, machine, got)
        assert halted is None
        local_cases += 1
    statistics["exhaustive_local_boundary_cases"] = local_cases

    # One-step checks on arbitrary cyclic tables and configurations.
    random_cases = 0
    for _ in range(20):
        n = rng.randrange(1, 9)
        transitions = {(state, bit): (rng.randrange(2), rng.choice(("L", "R")),
                                     rng.randrange(n+1))
                       for state in range(n) for bit in (0, 1)
                       if rng.randrange(5)}
        t = Terms()
        core = interpreter(t)
        machine = compile_machine(t, core, 0, transitions)
        for _ in range(10):
            native = (rng.randrange(len(machine["states"])),
                      [rng.randrange(2) for _ in range(rng.randrange(5))],
                      rng.randrange(2),
                      [rng.randrange(2) for _ in range(rng.randrange(5))])
            got, _ = sk_step(t, core, machine, native)
            assert got == native_step(transitions, native)
            random_cases += 1
    statistics["random_cyclic_configuration_steps"] = random_cases

    # Actual 253-state table: compare 300 successive exact configurations.
    here = Path(__file__).resolve().parent
    start, transitions = parse_tm(here / "literal_zfc253.tm")
    t = Terms()
    core = interpreter(t)
    machine = compile_machine(t, core, start, transitions)
    native = (start, [], 0, [])
    actual_steps, contractions = 0, 0
    for _ in range(300):
        expected = native_step(transitions, native)
        got, steps = sk_step(t, core, machine, native)
        assert got == expected
        contractions += steps
        if expected is None:
            break
        actual_steps += 1
        native = expected
    statistics["literal253_exact_steps"] = actual_steps
    statistics["literal253_transition_core_contractions"] = contractions
    statistics["literal253_after_trace"] = {
        "state": native[0], "left_nearest_first": native[1],
        "scanned_bit": native[2], "right_nearest_first": native[3]}

    # Independent parser and exact-reduction transport over all terms <=5 leaves.
    terms = small_terms(5)
    edges = 0
    for term in terms:
        ordinary = full_tree_reducts(term)
        translated = full_tree_reducts(one_encode(term), True)
        assert translated == {one_encode(result) for result in ordinary}
        edges += len(ordinary)
    statistics["one_constant_transport_terms_exhaustive"] = len(terms)
    statistics["one_constant_transport_reduction_edges"] = edges

    bcl = (here / "P253.bcl").read_text()
    assert t.parse_bcl(bcl) == machine["P"]
    one = (here / "P253.one.btree").read_text()
    assert decode_carrier_tree(parse_tree_bits(one)) == bcl
    statistics["full_payload_roundtrips"] = ["BCL", "one-constant -> BCL"]
    for name, expected_bits in (("P253.bcl", bcl), ("P253.one.btree", one)):
        unpacked = "".join(f"{byte:08b}" for byte in (here / (name+".bin")).read_bytes())
        assert unpacked[:len(expected_bits)] == expected_bits
        assert "1" not in unpacked[len(expected_bits):]
    statistics["packed_payload_roundtrips"] = "both passed, including zero padding"
    statistics["scope"] = ("Finite executable checks, not a proof-assistant "
                           "verification and not a consistency or infinite-run proof.")
    (here / "validation.json").write_text(json.dumps(statistics, indent=2)+"\n")
    print(json.dumps(statistics, indent=2))


if __name__ == "__main__":
    main()
