#!/usr/bin/env python3
"""The complete E639 equational packet, independent of ancestor Python code.

New reduction: replace the class projection V(b,d) by the descriptor b itself.
The masking-spine proof in e639_section.tex supplies the changed calibration.
This program checks syntax, exact packet accounting, Boolean identities and
finite coordinate regressions. It is not a Turing-machine compiler or a
formal-kernel check of the inherited raw-EPSC consistency calibration.

The unchanged signature, six first equations, Boolean closure kernel and
codec are inherited from the E663/E667 ProveIt packet at commit 0128d662fd.
Sh1 is due to McCune--Veroff--Fitelson--Harris--Feist--Wos (2002).
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

SIGNATURE = (("d", 0), ("N", 2), ("V", 2), ("P", 2), ("A", 2),
             ("Q", 1), ("W", 2), ("p_E", 2), ("p_eps", 2))
D = ("d",)
E663_PIN = "6c3b72c39c81aa5bbf028e654c8056e7e86376cdeecdd56943e5c3e23de1a215"


def t(op, *args):
    return (op, *args)


def n(x, y):
    return t("N", x, y)


def p(x, y):
    return t("P", x, y)


def closure(d, r, e, f, a, b, c, u, v):
    k = n(c, n(a, n(d, b)))
    h = n(n(n(d, u), k), n(u, v))
    not_bad = n(r, n(d, n(e, n(d, f))))
    return n(not_bad, n(d, h))


def presentation(direct=True):
    pe = lambda x, y: t("p_E", x, y)
    rho = lambda x, y: t("p_eps", p(y, p(x, "b")), "b" if direct else t("V", "b", D))
    h = t("Q", "b")
    nxt = lambda z: p("b", z)
    sep = lambda z: t("A", "b", z)
    r, e, f = rho(h, nxt("z")), pe(sep("z"), nxt("z")), pe(sep("z"), "z")
    a, b0, c = pe(t("W", "x", D), "x"), pe("x", h), rho("x", "y")
    u, v = pe("y", h), rho(nxt("y"), "y")
    return {
        "signature": SIGNATURE,
        "equations": (
            (n(n("x", n(n("y", "x"), "x")), n("y", n("z", "x"))), "y"),
            (t("V", p("x", "s"), D), "x"),
            (t("V", p("x", "s"), t("Q", "j")), t("V", "s", "j")),
            (t("p_eps", "s", p("a", "b")), n(t("p_eps", "s", "a"), t("p_eps", "s", "b"))),
            (t("p_eps", "s", t("A", "i", "j")), pe(t("V", "s", "i"), t("V", "s", "j"))),
            (t("p_eps", "s", t("Q", "a")),
             n(t("p_eps", p(t("W", "s", "a"), "s"), "a"), t("p_eps", p("z", "s"), "a"))),
            (D, closure(D, r, e, f, a, b0, c, u, v)),
        ),
        "start": t("Q", D),
        "target": D,
    }


def variables(term):
    if isinstance(term, str):
        return {term}
    return set().union(*(variables(s) for s in term[1:]))


def size(term):
    return 1 if isinstance(term, str) else 1 + sum(size(c) for c in term[1:])


def pretty(term):
    if isinstance(term, str):
        return term
    return term[0] + ("(" + ",".join(pretty(c) for c in term[1:]) + ")" if len(term) > 1 else "")


def encode(packet):
    sig = packet["signature"]
    arities = dict(sig)
    eqs = packet["equations"]
    cap = max(len(variables(a) | variables(b)) for a, b in eqs)
    width = max(1, (len(sig) + cap - 1).bit_length())
    opcodes = {op: i + cap for i, (op, _) in enumerate(sig)}

    def term_bits(ast, names):
        if isinstance(ast, str):
            return format(names[ast], f"0{width}b")
        if ast[0] not in arities or len(ast) != arities[ast[0]] + 1:
            raise ValueError("invalid source term")
        return format(opcodes[ast[0]], f"0{width}b") + "".join(term_bits(c, names) for c in ast[1:])

    header = format(len(sig), "08b") + "".join(format(a, "03b") for _, a in sig) + format(cap, "08b")
    body = ""
    for left, right in eqs:
        names = {v: i for i, v in enumerate(sorted(variables(left) | variables(right)))}
        body += "1" + term_bits(left, names) + term_bits(right, names)
    body += "0"
    endpoint_bits = term_bits(packet["start"], {}) + term_bits(packet["target"], {})
    bits = header + body + endpoint_bits
    metrics = {
        "operation_symbols": len(sig), "equations": len(eqs), "variable_capacity": cap,
        "opcode_bits": width, "equation_node_counts": [size(a) + size(b) for a, b in eqs],
        "equation_nodes": sum(size(a) + size(b) for a, b in eqs),
        "header_bits": len(header), "equation_bits": len(body), "endpoint_bits": len(endpoint_bits),
        "packet_bits": len(bits), "bit_character_sha256": hashlib.sha256(bits.encode("ascii")).hexdigest(),
    }
    return bits, metrics


def decode(bits):
    """Independent strict decoder; source symbol names and AST are unavailable."""
    cursor = 0

    def read(width):
        nonlocal cursor
        s = bits[cursor:cursor + width]
        if len(s) != width or any(c not in "01" for c in s):
            raise ValueError("invalid/truncated packet")
        cursor += width
        return int(s, 2)

    nops = read(8)
    arities = [read(3) for _ in range(nops)]
    cap = read(8)
    width = max(1, (nops + cap - 1).bit_length())

    def node():
        op = read(width)
        if op < cap:
            return op
        op -= cap
        if op >= nops:
            raise ValueError("unused opcode")
        return (op, *(node() for _ in range(arities[op])))

    equations = []
    while read(1):
        equations.append((node(), node()))
    start, target = node(), node()

    def ground(ast):
        return isinstance(ast, tuple) and all(ground(c) for c in ast[1:])

    if cursor != len(bits) or not ground(start) or not ground(target):
        raise ValueError("trailing data or nonground endpoint")
    return arities, cap, equations, start, target


def validate_packet(packet, bits):
    sig = [op for op, _ in packet["signature"]]

    def numeric(ast, names):
        return names[ast] if isinstance(ast, str) else (sig.index(ast[0]), *(numeric(c, names) for c in ast[1:]))

    eqs = []
    for left, right in packet["equations"]:
        names = {v: i for i, v in enumerate(sorted(variables(left) | variables(right)))}
        eqs.append((numeric(left, names), numeric(right, names)))
    expected = ([a for _, a in packet["signature"]], 4, eqs,
                numeric(packet["start"], {}), numeric(packet["target"], {}))
    assert decode(bits) == expected
    malformed = [bits[:i] for i in range(len(bits))]
    malformed += [bits + "0", bits[:-1] + "x", bits[:-4] + "0000"]
    for bad in malformed:
        try:
            decode(bad)
        except (ValueError, RecursionError):
            continue
        raise AssertionError("malformed packet accepted")
    return {"independent_roundtrip": True, "strict_truncations_rejected": len(bits),
            "additional_malformed_rejected": 3}


def mask_tail(parameters):
    tail = p(D, p(D, D))
    for a in reversed(parameters):
        tail = p(a, p(a, tail))
    return tail


def mask_descriptor(code, parameters):
    return p(p(code, code), mask_tail(parameters))


def regressions():
    """Transcription checks, not substitutes for the all-model mathematical proof."""
    # All independent Boolean valuations through seven parameter payloads;
    # no assumption that the class associated with d is true or false.
    masks = 0
    for count in range(8):
        names = [f"p{i}" for i in range(count)]
        s = mask_tail(names)
        b = mask_descriptor("c", names)
        for values in itertools.product((False, True), repeat=count + 2):
            env = dict(zip(["d", "c", *names], values))

            def eps(ast):
                if isinstance(ast, str):
                    return env[ast]
                if ast == D:
                    return env["d"]
                assert ast[0] == "P"
                return not (eps(ast[1]) and eps(ast[2]))

            assert eps(s) is True
            assert eps(b) == env["c"]
            masks += 1

    # The same masking identities in the eight-element powerset Boolean
    # algebra, with all choices of class d, code c, and two payloads.
    mask = 7
    finite_algebra = 0
    for d, c, a, b in itertools.product(range(8), repeat=4):
        nand = lambda x, y: mask ^ (x & y)
        true_tail = nand(d, nand(d, d))
        tail_b = nand(b, nand(b, true_tail))
        tail_a = nand(a, nand(a, tail_b))
        descriptor = nand(nand(c, c), tail_a)
        assert true_tail == tail_b == tail_a == mask
        assert descriptor == c
        finite_algebra += 1

    def selector(index):
        result = D
        for _ in range(index):
            result = t("Q", result)
        return result

    def lookup(stream, index):
        # Native Head/Tail equations as equations on free constructor trees.
        while isinstance(index, tuple) and index[0] == "Q":
            if not isinstance(stream, tuple) or stream[0] != "P":
                return D
            stream, index = stream[2], index[1]
        return stream[1] if isinstance(stream, tuple) and stream[0] == "P" else D

    coordinates = 0
    for count in range(33):
        args = [f"p{i}" for i in range(count)]
        code = t("A", selector(0), selector(1))
        b = mask_descriptor(code, args)
        stream = p("y", p("x", b))
        assert lookup(stream, selector(0)) == "y"
        assert lookup(stream, selector(1)) == "x"
        assert lookup(stream, selector(2)) == p(code, code)
        coordinates += 3
        for i, arg in enumerate(args):
            assert lookup(stream, selector(3 + 2 * i)) == arg
            assert lookup(stream, selector(4 + 2 * i)) == arg
            coordinates += 2

    # The closure cofactor that forces d=1 is unchanged.
    names = ("d", "r", "e", "f", "a", "b", "c", "u", "v")
    kernel = closure(*names)
    bool_cases = 0
    for values in itertools.product((False, True), repeat=9):
        env = dict(zip(names, values))

        def run(ast):
            return env[ast] if isinstance(ast, str) else not (run(ast[1]) and run(ast[2]))

        out = run(kernel)
        d, r, e, f, a, b, c, u, v = values
        assert ((not d) and out) == ((not d) and r)
        assert not (r and d == out) or d
        if d:
            target = (r and e and not f) or ((a or not c or u) and (not b or not c or u) and (not u or v))
            assert out == target
        bool_cases += 1
    return {"masking_boolean_assignments": masks,
            "masking_eight_element_boolean_algebra_assignments": finite_algebra,
            "coordinate_identities": coordinates,
            "closure_cofactor_assignments": bool_cases,
            "scope": "syntax, Boolean identities and coordinate regressions; no finite consistency claim"}


def write_packet(out, packet):
    bits, metrics = encode(packet)
    validation = validate_packet(packet, bits)
    padding = (-len(bits)) % 8
    packed = int(bits + "0" * padding, 2).to_bytes((len(bits) + padding) // 8, "big")
    assert "".join(f"{b:08b}" for b in packed)[:len(bits)] == bits
    (out / "E639.bits").write_text(bits + "\n")
    (out / "E639.bin").write_bytes(packed)
    (out / "E639.bitlength").write_text(str(len(bits)) + "\n")
    (out / "E639.equations").write_text("\n".join(f"{i}: {pretty(a)} = {pretty(b)}" for i, (a, b) in enumerate(packet["equations"], 1)) + "\nquery: " + pretty(packet["start"]) + " = " + pretty(packet["target"]) + "\n")
    (out / "E639.json").write_text(json.dumps({"name": "E639", **packet, "metrics": metrics,
        "transport_padding_bits": padding,
        "status": "complete equational consistency packet; ordinary inherited calibration; no TM state claim"}, indent=2) + "\n")
    return metrics, validation


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    parser.add_argument("--baseline-bits", type=Path,
        help="Optional retained E663.bits; if supplied it must match exact reconstruction")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if not __debug__:
        raise RuntimeError("run without Python -O")
    old = presentation(direct=False)
    old_bits, old_metrics = encode(old)
    assert old_metrics["packet_bits"] == 663
    assert old_metrics["bit_character_sha256"] == E663_PIN
    validate_packet(old, old_bits)
    if args.baseline_bits is not None:
        assert args.baseline_bits.read_text().strip() == old_bits
    new = presentation(direct=True)
    assert new["signature"] == old["signature"]
    assert new["equations"][:6] == old["equations"][:6]
    assert new["start"] == old["start"] and new["target"] == old["target"]
    metrics, validation = write_packet(args.out, new)
    assert metrics["packet_bits"] == 639
    assert metrics["equation_node_counts"] == [14, 6, 9, 12, 12, 17, 74]
    assert metrics["equation_nodes"] == 144
    assert old_metrics["equation_nodes"] - metrics["equation_nodes"] == 6
    recipe = {
        "truth_class": p(D, p(D, D)),
        "masking_base": "S_empty=P(d,P(d,d))",
        "masking_step": "S_(p::params)=P(p,P(p,S_params))",
        "descriptor": "b=P(P(c,c),S_params)",
        "relation": "R_b(x,y)=p_eps(P(y,P(x,b)),b)",
        "coordinates_zero_based": {"output": 0, "input": 1, "unused_code": 2,
                                   "parameter_i_for_i_zero_based": "3+2*i", "duplicate": "4+2*i"},
        "upper_model_weights": {"leaves": 1, "Q(b)": "w(b)+1",
                                "P(b,z)": "w(b)+w(z)+2", "A(b,z)": "w(b)+w(z)+3"},
        "proof_scope": "ordinary all-model argument; finite tests check transcription only"
    }
    (args.out / "masking_recipe.json").write_text(json.dumps(recipe, indent=2) + "\n")
    receipt = {
        "E663_reconstructed": old_metrics,
        "E663_optional_supplied_bits_checked": args.baseline_bits is not None,
        "E639": metrics, "validation": validation, "regressions": regressions(),
        "exact_reduction": {"class_projection_occurrences_removed": 3, "nodes_per_occurrence_saved": 2,
                            "term_nodes_saved": 6, "bits_saved": 24},
        "relative_theorem": "E639 has a nontrivial model iff raw EPSC has a model iff E663 has a nontrivial model",
        "calibration_dependency": "ordinary raw-EPSC/ZFC comparison inherited from ProveIt Sources 08 and 14",
        "new_TM_state_bound": None,
    }
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
