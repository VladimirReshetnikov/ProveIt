#!/usr/bin/env python3
"""Reproduce the independent finite binder/wire audit.

Run with Python 3 from any directory. This records regression evidence only;
it does not establish consistency, a formal soundness theorem, or a TM bound.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
import binder_kernel as k
import binder_wire as wire
import test_binder_kernel as fixtures


def value_paths(value, prefix=()):
    yield prefix
    if isinstance(value, dict):
        for key, child in value.items():
            yield from value_paths(child, prefix + (key,))
    elif isinstance(value, list):
        for key, child in enumerate(value):
            yield from value_paths(child, prefix + (key,))


def run():
    rng = random.Random(10162026)
    example = fixtures.make_example()
    replacements = [None, False, True, -1, 0, 1, 1.0, 1.5, "", "bot", "mem",
                    "f", "b", "K", [], {}, [None], [0], ["bot"], {"rows": []}]
    mutation_checks = 0
    for path in value_paths(example):
        for replacement in replacements:
            document = copy.deepcopy(example)
            if not path:
                document = copy.deepcopy(replacement)
            else:
                target = document
                for key in path[:-1]:
                    target = target[key]
                target[path[-1]] = copy.deepcopy(replacement)
            assert k.accepts_refutation(document) is False, (path, replacement)
            mutation_checks += 1

    opening_checks = 0
    for _ in range(800):
        arena = k.Arena()
        # These are arbitrary one-slot bodies, not just outputs of close().
        body = fixtures.random_formula(arena, rng, 4, 1)
        name = rng.randrange(5)
        cert = k.produce(arena, body, k.Mode("open", name))
        opened = k.verify(arena, cert)
        assert arena.scoped(body, 1) and arena.scoped(opened)
        ui = arena.imp(arena.all(body), opened)
        n = rng.choice((1, 2, 3))
        domain = range(n)
        bits = rng.getrandbits(n * n)
        relation = lambda x, y: bool(bits & (1 << (n * x + y)))
        values = [rng.randrange(n) for _ in range(5)]
        assignment = lambda i: values[i]
        assert k.evaluate(arena, opened, domain, relation, assignment) == k.evaluate(
            arena, body, domain, relation, assignment, (values[name],))
        assert k.evaluate(arena, ui, domain, relation, assignment)
        opening_checks += 2

    # The reverse inverse law needs freshness; it is not used by the kernel.
    arena = k.Arena()
    body = arena.mem(k.B(0), k.F(0))
    opened = k.produce(arena, body, k.Mode("open", 0))["output"]
    reclosed = k.produce(arena, opened, k.Mode("close", 0))["output"]
    assert body != reclosed
    assert arena.nodes[reclosed] == ("mem", k.B(0), k.B(0))

    # Extend the actual identity/UI/GEN proof to exercise every wire opcode.
    arena, conclusions = k.check_document(example)
    atom = arena.mem(k.F(0), k.F(1))
    identity = conclusions[4]
    vacuous = k.produce(arena, identity, k.Mode("close", 4))
    closed = k.produce(arena, atom, k.Mode("close", 4))
    psc_modes = (k.Mode("plug", 2, 0, 3), k.Mode("plug", 1, 0, 4),
                 k.Mode("plug", 0, 1, 4))
    psc_witnesses = [k.produce(arena, atom, mode) for mode in psc_modes]
    lines = example["lines"] + [
        fixtures.line("UD", [identity, atom, 4], [vacuous, closed]),
        fixtures.line("C", [identity, atom]),
        fixtures.line("PSC", [atom], psc_witnesses),
    ]
    document = {"formulas": arena.nodes, "lines": lines}
    assert set(line["rule"] for line in lines) == set(wire.RULES)
    code = wire.encode(document)
    assert len(wire.check(code)[1]) == 11
    assert wire.encode(wire.decode(code)) == code
    assert not wire.accepts_refutation(code)

    wire_flips = wire_valid_flips = 0
    for original in (wire.encode(example), code):
        for i in range(len(original)):
            mutated = original[:i] + ("1" if original[i] == "0" else "0") + original[i+1:]
            assert not wire.accepts_refutation(mutated)
            try:
                wire.check(mutated)
            except k.Invalid:
                pass
            else:
                wire_valid_flips += 1
                assert wire.encode(wire.decode(mutated)) == mutated
            wire_flips += 1

    # Formula-table counts and proof opcodes cannot make any finite read loop infinite.
    # This finite check covers the first four levels of the specified shortlex order.
    assert [bin(n)[3:] for n in range(1, 16)] == [
        "", "0", "1", "00", "01", "10", "11", "000", "001", "010", "011",
        "100", "101", "110", "111"]

    source_files = ["binder_kernel.py", "binder_wire.py", "test_binder_kernel.py"]
    hashes = {name: hashlib.sha256((ROOT / "code" / name).read_bytes()).hexdigest()
              for name in source_files}
    return {
        "scope": "independent finite regression audit; no consistency or formal soundness claim",
        "success": True,
        "seed": 10162026,
        "json_single_field_mutations": mutation_checks,
        "json_mutations_accepted_as_refutations": 0,
        "unexpected_exceptions": 0,
        "arbitrary_one_slot_bodies": 800,
        "opening_semantics_and_ui_comparisons": opening_checks,
        "open_then_close_freshness_counterexample_confirmed": True,
        "all_eight_opcodes_roundtrip": True,
        "all_opcode_example_lines": 11,
        "all_opcode_example_bits": len(code),
        "single_bit_wire_mutations": wire_flips,
        "valid_wire_mutations_with_exact_roundtrip": wire_valid_flips,
        "wire_mutations_accepted_as_refutations": 0,
        "shortlex_first_fifteen_checked": True,
        "source_sha256": hashes,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    args.output.write_text(text)
    print(text, end="")
