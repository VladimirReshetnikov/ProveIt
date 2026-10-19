#!/usr/bin/env python3
"""Delete a derived top axiom from the exact inherited E713 packet.

This is an independent AST/codec implementation.  It imports no source builder.
The finite Boolean identity checked here is only one algebraic lemma in the
written proof; these checks are not a consistency test or a TM construction.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from hashlib import sha256
import itertools
import json
from pathlib import Path


PIN_JSON = "1462caafdb6b53cda35cb99133c5ad3b4fd9411b779fd1fe13064c6e6c65ecfa"
PIN_BITS = "3cd0c3d0fb8d8640cfef1f44e0c22d377dd930de88a94093a2ef7650e22c9e72"
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


def closure_polynomial(d, r, e, f, a, b, c, u, v):
    lower = N(d, N(c, N(a, N(d, b))))
    not_bad = N(r, N(d, N(e, N(d, f))))
    not_hull = N(N(lower, N(d, u)), N(u, N(d, v)))
    return N(not_bad, not_hull)


def literal_closure():
    h = term("Target", "b")
    nxt = lambda z: term("Next", "b", z)
    mem = lambda z: term("Mem", "b", z)
    rel = lambda x, y: term("p_E", x, y)
    rho = lambda x, y: term("p_eps", term("P", y, term("P", x, "b")), term("V", "b", D))
    p = closure_polynomial(D, rho(h, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z"),
                           rel(term("W", "x", D), "x"), rel("x", h), rho("x", "y"),
                           rel("y", h), rho(nxt("y"), "y"))
    return [D, p]


def eval_boolean(t, env):
    if isinstance(t, str):
        return env[t]
    if t[0] != "N":
        raise ValueError("not a Boolean polynomial")
    return 1 - (eval_boolean(t[1], env) & eval_boolean(t[2], env))


def check_top_forcing():
    names = ("d", "r", "e", "f", "a", "b", "c", "u", "v")
    polynomial = closure_polynomial(*names)
    checks = 0
    for values in itertools.product((0, 1), repeat=len(names)):
        env = dict(zip(names, values))
        result = eval_boolean(polynomial, env)
        assert ((1-env["d"]) & result) == ((1-env["d"]) & env["r"])
        if env["d"] == 0:
            assert result == env["r"]
        if env["r"] == 1 and env["d"] == result:
            assert env["d"] == 1
        checks += 1
    for value in (0, 1):
        assert (1-(value & (1-(value & value)))) == 1
    return {"boolean_polynomial": polynomial, "truth_table_rows": checks,
            "identity": "(not d) and F(d,r,e,f,a,b,c,u,v) = (not d) and r",
            "constant_true_class_identity_rows": 2,
            "status": "finite Boolean identity checks; written proof gives all-algebra consequence"}


def main():
    parser = argparse.ArgumentParser()
    here = Path(__file__).resolve().parent
    parser.add_argument("--input", type=Path, default=here / "reference/E713.json")
    parser.add_argument("--bits", type=Path, default=here / "reference/E713.bits")
    parser.add_argument("--out", type=Path, default=here / "generated")
    args = parser.parse_args()
    raw = args.input.read_bytes()
    assert sha256(raw).hexdigest() == PIN_JSON, "source JSON differs from pinned E713"
    original = json.loads(raw)
    source_bits, source_metrics = encode(original)
    assert sha256(source_bits.encode()).hexdigest() == PIN_BITS
    assert source_bits + "\n" == args.bits.read_text()
    assert source_metrics["complete_packet_bits"] == 713
    removed = original["equations"][1]
    assert removed == [D, N(D, N(D, D))]
    assert original["equations"][-1] == literal_closure(), "closure transcription mismatch"
    assert original["equations"][2] == [term("V", term("P", "x", "s"), D), "x"]
    assert original["equations"][4] == [term("p_eps", "s", term("P", "a", "b")),
                                      N(term("p_eps", "s", "a"), term("p_eps", "s", "b"))]
    reduced = deepcopy(original)
    reduced.pop("metrics", None)
    reduced["name"] = "E688"
    del reduced["equations"][1]
    reduced["status"] = ("complete equational packet; ordinary equivalence to E713 by a derived-top "
                         "lemma; no new TM or proof-assistant endpoint")
    bits, metrics = encode(reduced)
    assert metrics["complete_packet_bits"] == 688
    assert decode(bits) == expected_decoding(reduced, metrics["variable_capacity"])
    assert metrics["equation_node_counts"] == [14, 6, 10, 12, 12, 17, 82]
    for cut in range(len(bits)):
        try:
            decode(bits[:cut])
        except ValueError:
            pass
        else:
            raise AssertionError(("accepted truncation", cut))
    for malformed in (bits + "0", bits + "1", bits[:-1] + "x"):
        try:
            decode(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("accepted malformed packet")
    boolean = check_top_forcing()
    k = term("P", D, term("P", D, D))
    descriptor = term("P", k, D)
    ground_substitution = {"b": descriptor, "x": D, "y": D, "z": D}
    ground_equation = [subst(t, ground_substitution) for t in reduced["equations"][-1]]
    assert not any(vars_of(t) for t in ground_equation)
    recipe = {
        "constant_true_class": k, "descriptor": descriptor,
        "closure_substitution": ground_substitution,
        "closure_ground_instance": ground_equation,
        "explanation": "NAND class equation makes epsilon(s,k)=top; native head returns k; "
                       "the closure bad-branch matrix r is then top; Boolean identity forces d=top.",
        "certificate_scope": "finite ground-substitution recipe plus checked Boolean lemma, "
                             "not an expanded Sh1-only contextual rewrite trace",
    }
    reduced["metrics"] = metrics
    result = {"status": "PASS", "source_E713": source_metrics, "E688": metrics,
              "removed_equation": removed, "removed_tree_nodes": size(removed[0])+size(removed[1]),
              "saved_bits": 25, "identical_signature_endpoints_and_other_equations": True,
              "strict_truncations_rejected": len(bits), "malformed_inputs_rejected": 3,
              "Boolean_lemma": boolean,
              "formal_status": "ordinary mathematical equivalence with inherited E713; no Lean/PA endpoint or TM bound"}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "E688.json").write_text(json.dumps(reduced, indent=2) + "\n")
    (args.out / "E688.bits").write_text(bits + "\n")
    (args.out / "E688.equations").write_text("\n".join(
        f"{i+1}: {pretty(a)} = {pretty(b)}" for i, (a,b) in enumerate(reduced["equations"])) + "\n")
    (args.out / "top_forcing_recipe.json").write_text(json.dumps(recipe, indent=2) + "\n")
    (args.out / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], **metrics, "saved_bits": 25,
                      "Boolean_rows": boolean["truth_table_rows"],
                      "strict_truncations_rejected": len(bits)}, indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: checks use assertions.")
    main()
