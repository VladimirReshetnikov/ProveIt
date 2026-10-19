#!/usr/bin/env python3
"""Build and independently check the complete E667 equational packet.

No third-party modules, machine-state claims, or imported generator code.
The established codec and E692/E688 source presentations are attributed in
ATTRIBUTION.txt.  The new operation is removal of E692's derivable top axiom.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

SIGNATURE = [("d", 0), ("N", 2), ("V", 2), ("P", 2), ("A", 2),
             ("Q", 1), ("W", 2), ("p_E", 2), ("p_eps", 2)]
D = ("d",)


def t(symbol, *children):
    return (symbol,) + children


def nand(a, b):
    return t("N", a, b)


def closure(d, r, e, f, a, b0, c, u, v):
    """Literal 696/692 mux closure, valid without assuming d is top."""
    k = nand(c, nand(a, nand(d, b0)))
    h = nand(nand(nand(d, u), k), nand(u, v))
    not_bad = nand(r, nand(d, nand(e, nand(d, f))))
    return nand(not_bad, nand(d, h))


def presentation(include_truth=False, old_selector=False, old_hull=False,
                 unshared=False):
    rel = lambda a, b: t("p_E", a, b)
    rho = lambda a, b: t("p_eps", t("P", b, t("P", a, "b")), t("V", "b", D))
    hull_name, next_name, mem_name = (("Target", "Next", "Mem") if unshared
                                     else ("Q", "P", "A"))
    hull = t(hull_name, "b")
    nxt = lambda z: t(next_name, "b", z)
    mem = lambda z: t(mem_name, "b", z)
    r, e, f = rho(hull, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z")
    a, b0, c = rel(t("W", "x", D), "x"), rel("x", hull), rho("x", "y")
    u, v = rel("y", hull), rho(nxt("y"), "y")
    final = closure(D, r, e, f, a, b0, c, u, v)
    if old_hull:
        low = nand(D, nand(c, nand(a, nand(D, b0))))
        bad_neg = nand(r, nand(D, nand(e, nand(D, f))))
        hull_neg = nand(nand(low, nand(D, u)), nand(u, nand(D, v)))
        final = nand(bad_neg, hull_neg)
    eqs = [
        (nand(nand("x", nand(nand("y", "x"), "x")), nand("y", nand("z", "x"))), "y"),
        (t("V", t("P", "x", "s"), D), "x"),
        (t("V", t("P", "x", "s"), t("A", "j", D) if old_selector else t("Q", "j")), t("V", "s", "j")),
        (t("p_eps", "s", t("P", "a", "b")), nand(t("p_eps", "s", "a"), t("p_eps", "s", "b"))),
        (t("p_eps", "s", t("A", "i", "j")), rel(t("V", "s", "i"), t("V", "s", "j"))),
        (t("p_eps", "s", t("Q", "a")),
         nand(t("p_eps", t("P", t("W", "s", "a"), "s"), "a"), t("p_eps", t("P", "z", "s"), "a"))),
        (D, final),
    ]
    if include_truth:
        eqs.insert(1, (D, nand(D, nand(D, D))))
    sig = SIGNATURE.copy()
    if unshared:
        sig[7:7] = [("Target", 1), ("Next", 2), ("Mem", 2)]
    return {"signature": sig, "equations": eqs, "start": nand(D, D), "target": D}


def varset(term):
    if isinstance(term, str):
        return {term}
    return set().union(*(varset(child) for child in term[1:]))


def size(term):
    return 1 if isinstance(term, str) else 1 + sum(size(child) for child in term[1:])


def canonical(equation):
    names = {name: f"v{n}" for n, name in enumerate(sorted(varset(equation[0]) | varset(equation[1])))}
    def walk(term):
        return names[term] if isinstance(term, str) else (term[0], *(walk(c) for c in term[1:]))
    return tuple(map(walk, equation))


def pretty(term):
    if isinstance(term, str):
        return term
    return term[0] + ("(" + ",".join(map(pretty, term[1:])) + ")" if len(term) > 1 else "")


def encode(packet):
    sig = packet["signature"]
    arity = dict(sig)
    equations = list(map(canonical, packet["equations"]))
    cap = max(len(varset(left) | varset(right)) for left, right in equations)
    width = max(1, (len(sig) + cap - 1).bit_length())
    codes = {symbol: i + cap for i, (symbol, _) in enumerate(sig)}
    def term_bits(term):
        if isinstance(term, str):
            index = int(term[1:])
            assert 0 <= index < cap
            return format(index, f"0{width}b")
        assert len(term) == arity[term[0]] + 1
        return format(codes[term[0]], f"0{width}b") + "".join(term_bits(c) for c in term[1:])
    header = format(len(sig), "08b") + "".join(format(a, "03b") for _, a in sig) + format(cap, "08b")
    body = "".join("1" + term_bits(left) + term_bits(right) for left, right in equations) + "0"
    endpoints = term_bits(packet["start"]) + term_bits(packet["target"])
    bits = header + body + endpoints
    metrics = {"operation_symbols": len(sig), "equations": len(equations), "variable_capacity": cap,
               "opcode_bits": width, "equation_node_counts": [size(a) + size(b) for a, b in equations],
               "equation_nodes": sum(size(a) + size(b) for a, b in equations),
               "header_bits": len(header), "equation_bits": len(body), "endpoint_bits": len(endpoints),
               "packet_bits": len(bits), "bit_character_sha256": hashlib.sha256(bits.encode("ascii")).hexdigest()}
    return bits, metrics


def decode(bits):
    # This independent parser represents variables as integers and operation
    # indices as tuples; no generator presentation object is consulted.
    pos = 0
    def read(count):
        nonlocal pos
        field = bits[pos:pos + count]
        if len(field) != count or any(char not in "01" for char in field):
            raise ValueError("invalid or truncated field")
        pos += count
        return int(field, 2)
    count = read(8)
    arities = [read(3) for _ in range(count)]
    cap = read(8)
    width = max(1, (count + cap - 1).bit_length())
    def term():
        code = read(width)
        if code < cap:
            return code
        op = code - cap
        if op >= count:
            raise ValueError("unused opcode")
        return (op, *(term() for _ in range(arities[op])))
    equations = []
    while read(1):
        equations.append((term(), term()))
    start, target = term(), term()
    def ground(term):
        return isinstance(term, tuple) and all(ground(child) for child in term[1:])
    if pos != len(bits) or not ground(start) or not ground(target):
        raise ValueError("trailing data or nonground endpoints")
    return arities, cap, equations, start, target


def validate(packet, bits):
    symbols = [f for f, _ in packet["signature"]]
    def numeric(term):
        return int(term[1:]) if isinstance(term, str) else (symbols.index(term[0]), *(numeric(c) for c in term[1:]))
    expected = ([a for _, a in packet["signature"]], 4,
                [tuple(map(numeric, canonical(eq))) for eq in packet["equations"]],
                numeric(packet["start"]), numeric(packet["target"]))
    assert decode(bits) == expected
    malformed = [bits[:n] for n in range(len(bits))]
    malformed += [bits + "0", bits[:-1] + "x", bits[:-4] + "0000"]
    # Last control changes the target constant opcode into variable v0.
    for bad in malformed:
        try:
            decode(bad)
        except (ValueError, RecursionError):
            pass
        else:
            raise AssertionError("malformed packet accepted")
    return {"roundtrip": True, "strict_truncations_rejected": len(bits), "other_malformed_rejected": 3}


def boolean_checks():
    # Evaluate the exact generic closure tree under independent Boolean values.
    args = ("d", "r", "e", "f", "a", "b0", "c", "u", "v")
    tree = closure(*args)
    def evaluate(t, env):
        return env[t] if isinstance(t, str) else not (evaluate(t[1], env) and evaluate(t[2], env))
    cofactor = 0
    guard = 0
    for vals in itertools.product((False, True), repeat=len(args)):
        env = dict(zip(args, vals))
        d, r, e, f, a, b0, c, u, v = vals
        F = evaluate(tree, env)
        assert ((not d) and F) == ((not d) and r)
        assert not (r and d == F) or d
        cofactor += 1
        if d:
            expected = (r and e and not f) or ((a or not c or u) and (not b0 or not c or u) and (not u or v))
            assert F == expected
            guard += 1
    return {"cofactor_assignments": cofactor, "truth_forcing_implication_assignments": cofactor,
            "closure_translation_assignments": guard}


def write_packet(out, name, packet):
    bits, metrics = encode(packet)
    validation = validate(packet, bits)
    padding = (-len(bits)) % 8
    binary = int(bits + "0" * padding, 2).to_bytes((len(bits) + padding) // 8, "big")
    assert "".join(format(x, "08b") for x in binary)[:len(bits)] == bits
    data = {"name": name, **packet, "metrics": metrics, "transport_padding_bits": padding,
            "status": "complete equational consistency packet; no Turing-machine state count"}
    (out / f"{name}.json").write_text(json.dumps(data, indent=2) + "\n")
    (out / f"{name}.bits").write_text(bits + "\n")
    (out / f"{name}.bin").write_bytes(binary)
    (out / f"{name}.bitlength").write_text(str(len(bits)) + "\n")
    (out / f"{name}.equations").write_text("\n".join(f"{i}: {pretty(a)} = {pretty(b)}" for i, (a, b) in enumerate(packet["equations"], 1)) + "\n")
    return {**metrics, **validation}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    parser.add_argument("--reference", type=Path, default=Path(__file__).resolve().parent / "reference")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    packets = {"E667": presentation(), "E692": presentation(include_truth=True),
               "E688": presentation(old_selector=True, old_hull=True, unshared=True)}
    pins = {"E692": "477e5b5de0876ec2d784ca958540117bb2aef9121eaee670925ab2ee8e1455e7",
            "E688": "9518c474861557da085c76ef77dd4141eecfa0befaec66d90acc81ac39264d97"}
    comparisons = {}
    for name, pin in pins.items():
        bits, metrics = encode(packets[name])
        assert metrics["packet_bits"] == int(name[1:])
        assert metrics["bit_character_sha256"] == pin
        source = args.reference / f"{name}.bits"
        assert source.read_text().strip() == bits
        comparisons[name] = {"reconstructed_literal_baseline": True, "expected_bit_sha256": pin}
    e667 = write_packet(args.out, "E667", packets["E667"])
    assert e667["packet_bits"] == 667
    assert e667["equation_node_counts"] == [14, 6, 9, 12, 12, 17, 80]
    old = packets["E692"]["equations"]
    assert packets["E667"]["equations"] == old[:1] + old[2:]
    true_class = t("P", D, t("P", D, D))
    descriptor = t("P", true_class, D)
    recipe = {"constant_true_class": true_class, "descriptor": descriptor,
              "closure_substitution": {"b": descriptor, "x": D, "y": D, "z": D},
              "uses_equations": [1, 2, 4, 7],
              "new_relative_theorem": "E667 and E692 have exactly the same models and all equational consequences",
              "proof_artifact_scope": "ground substitution plus arbitrary-Boolean-algebra proof; no expanded Sh1 rewrite derivation"}
    (args.out / "truth_forcing_recipe.json").write_text(json.dumps(recipe, indent=2) + "\n")
    receipt = {"baseline_comparisons": comparisons, "E667": e667, "boolean_checks": boolean_checks(),
               "deleted_equation": "d=N(d,N(d,d))", "exact_saving_vs_E692_bits": 25,
               "exact_saving_vs_E688_bits": 21, "new_theory_bound": "none; same-model redundancy theorem"}
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
