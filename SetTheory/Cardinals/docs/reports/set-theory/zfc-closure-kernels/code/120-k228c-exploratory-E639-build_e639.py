#!/usr/bin/env python3
"""Build E639 by letting the descriptor itself carry its class code.

The unchanged E663 codec, first six equations, and ground query are retained.
Only the three class arguments V(b,d) in the closure equation become b.
This is a mathematical representation change, not a machine-state result.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

import inherited_e667 as e


def require(condition, message):
    if not condition:
        raise ValueError(message)


def presentation():
    old = e.presentation()
    old["start"] = e.t("Q", e.D)
    bits, metric = e.encode(old)
    require(metric["packet_bits"] == 663, "wrong inherited bit count")
    require(metric["bit_character_sha256"] ==
            "6c3b72c39c81aa5bbf028e654c8056e7e86376cdeecdd56943e5c3e23de1a215",
            "wrong inherited packet")
    changes = []

    def change(term, path=()):
        if isinstance(term, str):
            return term
        if term[0] == "p_eps" and term[2] == e.t("V", "b", e.D):
            changes.append(list(path) + [2])
            return e.t("p_eps", change(term[1], path + (1,)), "b")
        return (term[0], *(change(child, path + (i,))
                           for i, child in enumerate(term[1:], 1)))

    equations = list(old["equations"])
    equations[-1] = tuple(change(t, (i,)) for i, t in enumerate(equations[-1]))
    require(len(changes) == 3, "expected three changed class arguments")
    new = {**old, "equations": equations}
    return old, new, changes


def descriptor_checks():
    # These are exact propositional/coordinate checks, not finite equational models.
    truth_cases = []
    for c, l in itertools.product((False, True), repeat=2):
        nand = lambda x, y: not (x and y)
        tail = nand(l, nand(l, l))
        wrapped = nand(nand(c, c), tail)
        require(tail and wrapped == c, "descriptor Boolean identity failed")
        truth_cases.append({"c": c, "L": l, "tail": tail, "descriptor": wrapped})

    default = ("d",)
    pair = lambda x, y: ("P", x, y)

    def coord(s, n):
        for _ in range(n):
            s = s[2] if isinstance(s, tuple) and s[0] == "P" else default
        return s[1] if isinstance(s, tuple) and s[0] == "P" else default

    checks = 0
    for length in range(12):
        params = [("parameter", n) for n in range(length)]
        stream = default
        for value in reversed(params):
            stream = pair(value, stream)
        c = ("chosen_class",)
        descriptor = pair(pair(c, c), pair(stream, pair(stream, stream)))
        base = pair(("y",), pair(("x",), descriptor))
        expected = [("y",), ("x",), pair(c, c), stream, stream] + params
        for depth in range(7):
            env = base
            bound = [("bound", n) for n in range(depth)]
            for value in reversed(bound):
                env = pair(value, env)
            want = bound + expected
            for n, value in enumerate(want):
                require(coord(env, n) == value, "coordinate shift failed")
                checks += 1
            require(coord(env, len(want)) == default, "default tail failed")
            checks += 1
    return {"Boolean_assignments": truth_cases,
            "native_coordinate_checks": checks,
            "parameter_coordinates": "5+i before internal binders; 5+i+k under k binders"}


def independent_roundtrip(packet, bits):
    # The inherited decoder has no access to the generating presentation.
    arities, cap, equations, start, target = e.decode(bits)
    names = [name for name, _ in packet["signature"]]

    def numeric(t):
        if isinstance(t, str):
            return int(t[1:])
        return (names.index(t[0]), *(numeric(c) for c in t[1:]))

    expected = ([arity for _, arity in packet["signature"]], 4,
                [tuple(numeric(t) for t in e.canonical(eq)) for eq in packet["equations"]],
                numeric(packet["start"]), numeric(packet["target"]))
    require((arities, cap, equations, start, target) == expected, "roundtrip mismatch")
    rejected = 0
    controls = [bits[:n] for n in range(len(bits))]
    controls += [bits + "0", bits[:-1] + "x", bits[:-4] + "0000"]
    for malformed in controls:
        try:
            e.decode(malformed)
        except (ValueError, RecursionError):
            rejected += 1
        else:
            raise ValueError("strict malformed control accepted")
    return {"independent_AST_roundtrip": True,
            "strict_truncations_rejected": len(bits),
            "other_malformed_rejected": rejected - len(bits)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    old, new, changes = presentation()
    bits, metrics = e.encode(new)
    require(metrics["packet_bits"] == 639, "wrong final bit count")
    require(metrics["equation_node_counts"] == [14, 6, 9, 12, 12, 17, 74],
            "wrong equation counts")
    require(old["equations"][:6] == new["equations"][:6], "early equation changed")
    require(old["signature"] == new["signature"], "signature changed")
    require(old["start"] == new["start"] and old["target"] == new["target"], "query changed")
    validation = independent_roundtrip(new, bits)
    descriptor = descriptor_checks()
    cofactor = e.boolean_checks()
    padding = (-len(bits)) % 8
    binary = int(bits + "0" * padding, 2).to_bytes((len(bits) + padding) // 8, "big")
    require("".join(format(b, "08b") for b in binary)[:len(bits)] == bits, "transport mismatch")
    data = {"name": "E639", **new, "metrics": metrics,
            "transport_padding_bits": padding,
            "status": "calibrated equational packet by ordinary inherited model argument; no TM state claim"}
    (args.out / "E639.json").write_text(json.dumps(data, indent=2) + "\n")
    (args.out / "E639.bits").write_text(bits + "\n")
    (args.out / "E639.bin").write_bytes(binary)
    (args.out / "E639.bitlength").write_text(str(len(bits)) + "\n")
    (args.out / "E639.equations").write_text("\n".join(
        f"{i}: {e.pretty(a)} = {e.pretty(b)}"
        for i, (a, b) in enumerate(new["equations"], 1)) + "\nQUERY: Q(d) = d\n")
    result = {"status": "PASS", "new_packet": metrics,
              "old_packet_bits": 663, "saving_bits": 24,
              "removed_equation_term_nodes": 6,
              "changed_class_argument_paths_in_equation_7": changes,
              "unchanged_signature_first_six_equations_and_query": True,
              "validation": validation, "descriptor_checks": descriptor,
              "inherited_closure_Boolean_checks": cofactor,
              "proof_scope": "Ordinary ZFC-formalizable extraction and upper-model adaptation; no new Lean/Rocq theorem, PA translator, or binary interpreter",
              "new_descriptor": "R_b(x,y)=p_eps(P(y,P(x,b)),b)",
              "complete_descriptor_wrapper": "b=P(P(c,c),P(L,P(L,L)))",
              "truth_forcing_descriptor": "b*=P(d,P(d,d))",
              "binary_sha256": hashlib.sha256(binary).hexdigest()}
    (args.out / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
