#!/usr/bin/env python3
"""Finite, collision-sensitive checks of the complete shift-only proof kernel."""
from __future__ import annotations

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import statistics
import time

import four_kernel as old
import shift_kernel as k
import shift_proof_transport as transport
import shift_stream as stream
import fixed_search as fixed
import unary_search as unary


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def rejects(fn, *args):
    try:
        fn(*args)
    except (ValueError, TypeError, KeyError):
        return True
    return False


def shape(names):
    out = k.All(k.R(k.B(0), k.F(names[-1])))
    for i, name in enumerate(names):
        out = k.Imp(k.R(k.F(name), k.F(names[(i + 1) % len(names)])), out)
    return out


def verify():
    started = time.monotonic()
    root = Path(__file__).resolve().parent
    evidence = {"status": "PASS", "scope": "complete shift-only reference kernel and proof transport; 22 stream controls, no TM count"}
    distributions, total_maps, reverse_cases = [], 0, 0
    for n in range(1, 5):
        a = shape(list(range(n)))
        seed = {"instructions": [{"op": "K", "a": a, "b": k.BOT}]}
        theorem = k.check_certificate(seed)[0]
        lengths, back_lengths = [], []
        for image in product(range(n), repeat=n):
            mapping = dict(enumerate(image))
            converted, audit = transport.substitute_certificate(seed, mapping)
            lines = k.check_certificate(converted)
            require(lines[-1] == k.rename(theorem, mapping.__getitem__), "simultaneous theorem substitution")
            back = transport.reverse_translate(converted)
            require(old.check_certificate(back)[-1] == lines[-1], "reverse substitution proof")
            require(all(ins["op"] not in ("swap", "contract", "fused_down", "gen", "fresh_ui")
                        for ins in converted["instructions"]), "removed opcode leakage")
            lengths.append(len(lines) - 1)
            back_lengths.append(len(back["instructions"]))
            total_maps += 1
            reverse_cases += 1
        distributions.append({"n": n, "maps": n ** n,
                              "added_rows_mean": statistics.mean(lengths), "added_rows_max": max(lengths),
                              "reverse_rows_max": max(back_lengths)})
    evidence["exhaustive_theorem_substitutions"] = total_maps
    evidence["substitution_distributions"] = distributions

    rng = random.Random(2026101722)
    for _ in range(30):
        names = sorted(rng.sample(range(-4, 5), rng.randrange(1, 5)))
        a = shape(names)
        seed = {"instructions": [{"op": "K", "a": a, "b": k.BOT}]}
        mapping = {x: rng.randrange(-4, 5) for x in names}
        theorem = k.check_certificate(seed)[0]
        converted, _ = transport.substitute_certificate(seed, mapping)
        require(k.check_certificate(converted)[-1] == k.rename(theorem, mapping.__getitem__), "signed theorem map")
        back = transport.reverse_translate(converted)
        require(old.check_certificate(back)[-1] == converted["conclusion"], "signed reverse")
        reverse_cases += 1
    evidence["signed_theorem_substitutions"] = 30

    bodies = [k.R(k.B(0), k.F(0)),
              k.All(k.Imp(k.R(k.B(1), k.F(-2)), k.R(k.B(0), k.F(0)))),
              k.All(k.R(k.B(0), k.F(2))), k.BOT]
    forward_cases = 0
    for body in bodies:
        for name in (-3, -1, 0, 1, 3):
            source = old.make_ui_certificate(body, name)
            converted, _ = transport.translate(source)
            expected = k.Imp(k.All(body), k.open_body(body, name))
            require(k.check_certificate(converted)[-1] == expected, "arbitrary UI exact formula")
            require(old.check_certificate(transport.reverse_translate(converted))[-1] == expected, "UI roundtrip")
            forward_cases += 1
            reverse_cases += 1

    for name in (-3, -1, 0, 1, 3):
        a = shape([0, 2])
        source = {"instructions": [{"op": "K", "a": a, "b": k.BOT},
                                    {"op": "gen", "line": 0, "name": name}]}
        converted, _ = transport.translate(source)
        require(k.check_certificate(converted)[-1] == old.check_certificate(source)[-1], "named GEN exact formula")
        forward_cases += 1

    # Full UI0 deliberately permits the existing free0 and the entire source19 body.
    direct_ui = {"instructions": [{"op": "ui_zero", "body": old.source19_body()}]}
    expected_ui = k.Imp(k.All(old.source19_body()), k.open_body(old.source19_body(), 0))
    require(k.check_certificate(direct_ui) == [expected_ui], "one-row colliding UI0")
    direct_back = transport.reverse_translate(direct_ui)
    require(old.check_certificate(direct_back)[-1] == expected_ui, "one-row UI reverse")
    source19 = old.make_ui_certificate(old.source19_body(), 0)
    converted19, audit19 = transport.translate(source19)
    require(k.check_certificate(converted19)[-1] == expected_ui, "source19 compiled proof")
    evidence["source19_ui"] = {"old_rows": len(source19["instructions"]),
                               "generic_translated_rows": len(converted19["instructions"]),
                               "direct_shift22_rows": 1,
                               "reverse_of_direct_rows": len(direct_back["instructions"])}
    forward_cases += 1
    reverse_cases += 1

    # A compact actual theorem contraction: four rows beyond its input theorem.
    a = shape([0, 1])
    first = {"op": "K", "a": a, "b": k.BOT}
    original = k.check_certificate({"instructions": [first]})[0]
    closed = k.close_name(original, 0)
    moved_body = k.rename(closed, lambda x: x - 1)
    contraction = {"instructions": [first, {"op": "gen_zero", "line": 0},
                                      {"op": "ui_zero", "body": moved_body},
                                      {"op": "up", "line": 2},
                                      {"op": "mp", "implication": 3, "antecedent": 1}]}
    expected = k.rename(original, lambda x: 1 if x == 0 else x)
    require(k.check_certificate(contraction)[-1] == expected, "four-row contraction")
    require(old.check_certificate(transport.reverse_translate(contraction))[-1] == expected, "four-row contraction reverse")
    reverse_cases += 1
    evidence["compact_contraction_added_rows"] = 4

    # MP remapping, all unchanged logical schemas, signed renamings and final alias.
    a, b = shape([0, 1]), shape([-2, 2])
    instructions = [
        {"op": "K", "a": a, "b": k.Imp(a, a)},
        {"op": "K", "a": a, "b": a},
        {"op": "S", "a": a, "b": k.Imp(a, a), "c": a},
        {"op": "mp", "implication": 2, "antecedent": 0},
        {"op": "mp", "implication": 3, "antecedent": 1},
        {"op": "Peirce", "a": a, "b": b},
        {"op": "exfalso", "a": a},
        {"op": "distribution", "a": bodies[0], "b": k.BOT},
        {"op": "vacuity", "a": a},
        {"op": "axiom", "index": 0},
    ]
    for op in ("up", "down", "swap", "contract"):
        instructions.append({"op": op, "line": 4})
        instructions.append({"op": "gen", "line": len(instructions) - 1, "name": -2})
    instructions.append({"op": "swap", "line": 9})
    mixed, mixed_audit = transport.translate({"instructions": instructions}, [fixed.CP])
    require(k.check_certificate(mixed, [fixed.CP])[-1] == fixed.CP, "closed final alias")
    evidence["mixed_proof"] = {key: mixed_audit[key] for key in ("old_lines", "expanded_lines", "new_lines")}
    forward_cases += 1

    scanner_checks = 0
    for name in range(-30, 31):
        formula = k.All(k.Imp(k.R(k.B(0), k.F(name)), k.All(k.R(k.F(name), k.B(1)))))
        for mode, op in (("u", "up"), ("d", "down")):
            require(stream.transduce(mode, stream.encode(formula)) == stream.encode(k.rename_step(op, formula)), "shift scanner")
            scanner_checks += 1
    evidence["stream_control_states"] = {mode: stream.table(mode)["states"] for mode in "ud"}
    evidence["transducer_tables"] = {mode: stream.table(mode) for mode in "ud"}
    require(sum(evidence["stream_control_states"].values()) == 22, "stream control count")
    evidence["scanner_checks"] = scanner_checks

    matrices = [k.BOT, k.Imp(k.BOT, k.BOT), k.R(k.F(0), k.F(1)), k.All(k.R(k.B(0), k.F(2)))]
    axioms = [fixed.CP]
    for matrix in matrices:
        axioms.extend((fixed.gic_axiom(matrix), fixed.epsc2_axiom(matrix), unary.axiom(matrix)))
    for axiom in axioms:
        require(k.scoped(axiom) and not k.free_names(axiom), "fixed emitter closure")
        for op in k.RENAMINGS:
            require(k.rename_step(op, axiom) == axiom, "closed emitter changed by a shift")
    evidence["closed_frontend_axioms"] = len(axioms)

    negatives = 0
    for removed in ("swap", "contract", "fused_down", "gen", "fresh_ui", "fresh_ui_zero"):
        require(rejects(k.check_certificate, {"instructions": [first, {"op": removed, "line": 0, "name": 0, "fresh": 0, "body": bodies[0]}]}), "removed opcode accepted")
        negatives += 1
    bad = [
        {"instructions": [first, {"op": "gen_zero", "line": 0, "name": 0}]},
        {"instructions": [{"op": "ui_zero", "body": bodies[0], "fresh": 0}]},
        {"instructions": [{"op": "ui_zero", "body": k.R(k.B(1), k.F(0))}]},
        {"instructions": [{"op": "up", "line": 0}]},
    ]
    for certificate in bad:
        require(rejects(k.check_certificate, certificate), "malformed shift kernel accepted")
        negatives += 1
    require(rejects(k.check_certificate, {"instructions": [{"op": "axiom", "index": 0}]}, [a]), "open theory accepted")
    negatives += 1
    for checker in (fixed.check_refutation, unary.check_refutation):
        for candidate in ({"matrices": [], "proof": []},
                          {"matrices": [], "proof": [], "target": k.BOT},
                          {"matrices": [], "proof": [], "theory": [k.BOT]},
                          {"matrices": [], "proof": [first]}):
            require(rejects(checker, candidate), "fixed refutation interface accepted invalid input")
            negatives += 1
    for data in (b'', b'null', b'NaN', b'[]', b'{"matrices": [], "proof": []}', b'\xff'):
        require(not fixed.accepts_bytes(data) and not unary.accepts_bytes(data), "bad refutation bytes accepted")
        negatives += 2
    for data in (b'', b'\x00', b'\xff', b'hello', bytes(range(256))):
        require(fixed.shortlex_bytes_at(fixed.index_of_bytes(data)) == data, "shortlex roundtrip")
    evidence.update(forward_proof_cases=forward_cases, reverse_proof_cases=reverse_cases,
                    negative_interface_cases=negatives, shortlex_roundtrips=5,
                    samples={"one_row_source19_ui": direct_ui, "four_added_row_contraction": contraction},
                    elapsed_seconds=round(time.monotonic() - started, 6))
    evidence["code_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(root.glob("*.py"))}
    return evidence


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="shift22_results.json")
    args = parser.parse_args()
    result = verify()
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("status", "exhaustive_theorem_substitutions", "forward_proof_cases",
                                                 "reverse_proof_cases", "stream_control_states", "elapsed_seconds")}))
