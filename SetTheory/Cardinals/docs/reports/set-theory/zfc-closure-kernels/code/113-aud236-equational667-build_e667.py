#!/usr/bin/env python3
"""Combine E692 structural sharing with E688 derived truth to emit E667.

The AST/codec utilities below are adapted from the independently implemented
incoming build_e688.py (SHA-256 in ATTRIBUTION.txt); no upstream builder is
imported or executed. The new literal closure reconstruction is for E692,
whose optimized closure must be checked afresh without assuming d=top.
This is an equational problem, not a counted Turing-machine interpreter.
Checks use explicit exceptions and remain active under python -O.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from hashlib import sha256
import itertools
import json
from pathlib import Path


PIN_JSON = "0657cefef8f41bd7e463eb0adcd5a44b118de62ec852729202d3ecc4b6942d43"
PIN_BITS = "477e5b5de0876ec2d784ca958540117bb2aef9121eaee670925ab2ee8e1455e7"
D = ["d"]


def term(symbol, *children):
    return [symbol, *children]


def N(a, b):
    return term("N", a, b)


def vars_of(t):
    if isinstance(t, str):
        return {t}
    answer = set()
    for child in t[1:]:
        answer.update(vars_of(child))
    return answer


def size(t):
    return 1 if isinstance(t, str) else 1 + sum(size(c) for c in t[1:])


def subst(t, env):
    if isinstance(t, str):
        return deepcopy(env.get(t, t))
    return [t[0], *(subst(c, env) for c in t[1:])]


def pretty(t):
    if isinstance(t, str):
        return t
    return t[0] if len(t) == 1 else t[0] + "(" + ",".join(map(pretty, t[1:])) + ")"


def validate(data):
    signature = data["signature"]
    def visit(t):
        if isinstance(t, str):
            if not t or not t.isidentifier():
                raise ValueError("invalid variable")
            return
        if not isinstance(t, list) or not t or t[0] not in signature:
            raise ValueError("invalid symbol")
        if len(t) != signature[t[0]] + 1:
            raise ValueError("arity mismatch")
        for child in t[1:]:
            visit(child)
    if not (1 <= len(signature) < 256):
        raise ValueError("signature count")
    if any(not isinstance(a, int) or not 0 <= a < 8 for a in signature.values()):
        raise ValueError("signature arity")
    for equation in data["equations"]:
        if len(equation) != 2:
            raise ValueError("equation arity")
        for side in equation:
            visit(side)
    for label in ("start", "target"):
        visit(data[label])
        if vars_of(data[label]):
            raise ValueError("nonground endpoint")


def encode(data):
    validate(data)
    signature = list(data["signature"])
    capacity = max(len(vars_of(a) | vars_of(b)) for a, b in data["equations"])
    width = max(1, (len(signature) + capacity - 1).bit_length())
    codes = {name: capacity + i for i, name in enumerate(signature)}
    def emit(t, variables):
        if isinstance(t, str):
            return format(variables[t], f"0{width}b")
        return format(codes[t[0]], f"0{width}b") + "".join(emit(c, variables) for c in t[1:])
    header = (format(len(signature), "08b")
              + "".join(format(data["signature"][name], "03b") for name in signature)
              + format(capacity, "08b"))
    rows = []
    for left, right in data["equations"]:
        variables = {name: i for i, name in enumerate(sorted(vars_of(left) | vars_of(right)))}
        rows.append("1" + emit(left, variables) + emit(right, variables))
    equation_bits = "".join(rows) + "0"
    endpoint_bits = emit(data["start"], {}) + emit(data["target"], {})
    bits = header + equation_bits + endpoint_bits
    metrics = {
        "signature_symbols": len(signature), "variable_capacity": capacity,
        "opcode_width": width, "equations": len(rows),
        "both_side_tree_nodes": sum(size(a) + size(b) for a, b in data["equations"]),
        "equation_node_counts": [size(a) + size(b) for a, b in data["equations"]],
        "header_bits": len(header), "equation_bits": len(equation_bits),
        "endpoint_bits": len(endpoint_bits), "complete_packet_bits": len(bits),
        "bits_sha256": sha256(bits.encode("ascii")).hexdigest(),
    }
    return bits, metrics


def decode(bits):
    if any(c not in "01" for c in bits):
        raise ValueError("nonbit input")
    cursor = 0
    def read(n):
        nonlocal cursor
        if cursor + n > len(bits):
            raise ValueError("truncated input")
        value = int(bits[cursor:cursor+n], 2)
        cursor += n
        return value
    symbols = read(8)
    if symbols == 0:
        raise ValueError("empty signature")
    arities = [read(3) for _ in range(symbols)]
    capacity = read(8)
    width = max(1, (symbols + capacity - 1).bit_length())
    def parse():
        code = read(width)
        if code < capacity:
            return "v" + str(code)
        symbol = code - capacity
        if not 0 <= symbol < symbols:
            raise ValueError("unused opcode")
        return [symbol, *(parse() for _ in range(arities[symbol]))]
    equations = []
    while read(1):
        equations.append([parse(), parse()])
    start, target = parse(), parse()
    if cursor != len(bits):
        raise ValueError("trailing input")
    if vars_of(start) or vars_of(target):
        raise ValueError("nonground endpoint")
    return arities, capacity, equations, start, target


def expected_decoding(data, capacity):
    symbols = {s: i for i, s in enumerate(data["signature"])}
    def convert(t, v):
        if isinstance(t, str):
            return v[t]
        return [symbols[t[0]], *(convert(c, v) for c in t[1:])]
    equations = []
    for a, b in data["equations"]:
        v = {x: "v" + str(i) for i, x in enumerate(sorted(vars_of(a) | vars_of(b)))}
        equations.append([convert(a, v), convert(b, v)])
    return (list(data["signature"].values()), capacity, equations,
            convert(data["start"], {}), convert(data["target"], {}))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def closure_polynomial(d, r, e, f, a, b, c, u, v):
    """Exact E692 optimized closure, with d kept an independent argument."""
    not_lower = N(c, N(a, N(d, b)))
    hull = N(N(N(d, u), not_lower), N(u, v))
    not_bad = N(r, N(d, N(e, N(d, f))))
    return N(not_bad, N(d, hull))


def literal_closure():
    h = term("Q", "b")
    nxt = lambda z: term("P", "b", z)
    mem = lambda z: term("A", "b", z)
    rel = lambda x, y: term("p_E", x, y)
    rho = lambda x, y: term("p_eps", term("P", y, term("P", x, "b")), term("V", "b", D))
    rhs = closure_polynomial(D, rho(h, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z"),
                             rel(term("W", "x", D), "x"), rel("x", h), rho("x", "y"),
                             rel("y", h), rho(nxt("y"), "y"))
    return [D, rhs]


def eval_boolean(t, env):
    if isinstance(t, str):
        return env[t]
    require(t[0] == "N", "Not a Boolean polynomial")
    return 1 - (eval_boolean(t[1], env) & eval_boolean(t[2], env))


def cofactor_checks():
    names = "d r e f a b c u v".split()
    polynomial = closure_polynomial(*names)
    rows, forced_top_rows = 0, 0
    for values in itertools.product((0, 1), repeat=len(names)):
        env = dict(zip(names, values))
        result = eval_boolean(polynomial, env)
        require(((1-env["d"]) & result) == ((1-env["d"]) & env["r"]), "Cofactor identity")
        if env["d"] == 0:
            require(result == env["r"], "Zero cofactor")
        if env["r"] == 1 and env["d"] == result:
            require(env["d"] == 1, "Truth forcing")
            forced_top_rows += 1
        rows += 1
    for value in (0, 1):
        require(1-(value & (1-(value & value))) == 1, "True-class Boolean identity")
    return dict(status="PASS", independent_Boolean_arguments=names,
                truth_table_rows=rows, top_forcing_applicable_rows=forced_top_rows,
                constant_true_class_rows=2, polynomial=polynomial,
                identity="(not d) and G(d,r,e,f,a,b,c,u,v) = (not d) and r",
                scope="Finite Boolean polynomial checks; the written cofactor proof covers all Boolean algebras.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument("--input", type=Path, default=here / "reference/E692.json")
    parser.add_argument("--bits", type=Path, default=here / "reference/E692.bits")
    parser.add_argument("--out", type=Path, default=here / "generated")
    args = parser.parse_args()
    raw = args.input.read_bytes()
    require(sha256(raw).hexdigest() == PIN_JSON, "Source E692 JSON differs from pin")
    original = json.loads(raw)
    source_bits, source_metrics = encode(original)
    require(sha256(source_bits.encode()).hexdigest() == PIN_BITS, "Source E692 bits differ from pin")
    require(source_bits + "\n" == args.bits.read_text(), "Source E692 bit file differs")
    require(source_metrics["complete_packet_bits"] == 692, "Source length")
    require(original["equations"][-1] == literal_closure(), "Exact optimized closure reconstruction")
    require(original["equations"][2] == [term("V", term("P", "x", "s"), D), "x"], "Head equation")
    require(original["equations"][3] == [term("V", term("P", "x", "s"), term("Q", "j")), term("V", "s", "j")],
            "Unary selector equation must be preserved")
    require(original["equations"][4] == [term("p_eps", "s", term("P", "a", "b")),
                                         N(term("p_eps", "s", "a"), term("p_eps", "s", "b"))], "NAND class equation")
    removed = original["equations"][1]
    require(removed == [D, N(D, N(D, D))], "Exact truth equation")
    reduced = deepcopy(original)
    reduced.pop("metrics", None)
    reduced["name"] = "E667"
    del reduced["equations"][1]
    reduced["status"] = "complete equational packet; ordinary same-model equivalence to E692 by derived truth; no TM state bound"
    reduced["truth_optimization"] = "d=top derived from retained optimized closure, head, NAND class, and Sh1"
    bits, metrics = encode(reduced)
    require(metrics["complete_packet_bits"] == 667, "Reduced length")
    require(metrics["equation_node_counts"] == [14, 6, 9, 12, 12, 17, 80], "Equation node counts")
    require(decode(bits) == expected_decoding(reduced, metrics["variable_capacity"]), "Independent codec roundtrip")
    require(reduced["signature"] == original["signature"] and reduced["start"] == original["start"]
            and reduced["target"] == original["target"], "Signature/endpoints altered")
    require(reduced["equations"] == original["equations"][:1] + original["equations"][2:], "Other equations altered")
    for cut in range(len(bits)):
        try:
            decode(bits[:cut])
        except ValueError:
            pass
        else:
            raise ValueError("Accepted strict prefix at length " + str(cut))
    for malformed in (bits + "0", bits + "1", bits[:-1] + "x"):
        try:
            decode(malformed)
        except ValueError:
            pass
        else:
            raise ValueError("Accepted malformed packet")
    boolean = cofactor_checks()
    k = term("P", D, term("P", D, D))
    descriptor = term("P", k, D)
    ground_substitution = {"b": descriptor, "x": D, "y": D, "z": D}
    ground_equation = [subst(t, ground_substitution) for t in reduced["equations"][-1]]
    require(not any(vars_of(t) for t in ground_equation), "Ground closure instance contains variables")
    r = term("p_eps", term("P", term("P", descriptor, D),
                           term("P", term("Q", descriptor), descriptor)), term("V", descriptor, D))
    r_head_reduced = deepcopy(r)
    r_head_reduced[2] = k
    recipe = dict(constant_true_class=k, descriptor=descriptor,
                  closure_substitution=ground_substitution, closure_ground_instance=ground_equation,
                  bad_branch_matrix_ground_instance=r, bad_branch_matrix_after_head=r_head_reduced,
                  explanation="NAND class forces epsilon(s,k)=Boolean top; head returns k; closure r=top; cofactor forces d=top.",
                  scope="Ground-substitution recipe plus finite Boolean certificate; not an expanded Sh1-only equational rewrite trace.")
    pad = (-len(bits)) % 8
    packed_bits = bits + "0" * pad
    packed = bytes(int(packed_bits[i:i+8], 2) for i in range(0, len(packed_bits), 8))
    require("".join(format(b, "08b") for b in packed)[:len(bits)] == bits, "Packed-byte roundtrip")
    metrics.update(packed_bytes=len(packed), trailing_padding_bits=pad)
    reduced["metrics"] = metrics
    receipt = dict(status="PASS", source_E692=source_metrics, E667=metrics,
                   source_json_sha256=PIN_JSON, removed_equation=removed,
                   removed_tree_nodes=size(removed[0])+size(removed[1]), saved_bits=25,
                   identical_signature_endpoints_and_other_equations=True,
                   strict_truncations_rejected=len(bits), malformed_inputs_rejected=3,
                   Boolean_cofactor=boolean, checker_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   formal_status="Ordinary same-model equivalence with E692; inherits its ZFC calibration; no new kernel endpoint or TM bound.")
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "E667.json").write_text(json.dumps(reduced, indent=2) + "\n")
    (args.out / "E667.bits").write_text(bits + "\n")
    (args.out / "E667.bin").write_bytes(packed)
    (args.out / "E667.bitlength").write_text(str(len(bits)) + "\n")
    (args.out / "E667.equations").write_text("\n".join(
        f"{i+1}: {pretty(a)} = {pretty(b)}" for i, (a,b) in enumerate(reduced["equations"])) + "\n")
    (args.out / "truth_derivation_recipe.json").write_text(json.dumps(recipe, indent=2) + "\n")
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(dict(status="PASS", **metrics, saved_bits=25, Boolean_rows=boolean["truth_table_rows"]), indent=2))


if __name__ == "__main__":
    main()


