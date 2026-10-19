#!/usr/bin/env python3
"""Reconstruct E713; witness sharing E704; Boolean E696; unary selector E692.

The exact E713 term trees and codec are inherited from the pinned 2026-10-19
ProveIt intake.  The new transformation is Target=Q, Next=P, Mem=A on that
packet.  The proof in combination704.tex treats Q as existential negation.
This script emits an equational consistency problem, not a Turing machine.
Python standard library only.  See ATTRIBUTION.txt and sources.json.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

D = ("d",)
ALIASES = {"Target": "Q", "Next": "P", "Mem": "A"}


def T(f, *args):
    return (f, *args)


def N(x, y):
    return T("N", x, y)


def neg(x):
    return N(D, x)


def meet(x, y):
    return neg(N(x, y))


def variables(t):
    return {t} if isinstance(t, str) else set().union(*(variables(u) for u in t[1:]))


def nodes(t):
    return 1 if isinstance(t, str) else 1 + sum(map(nodes, t[1:]))


def pretty(t):
    if isinstance(t, str):
        return t
    return t[0] if len(t) == 1 else t[0] + "(" + ",".join(map(pretty, t[1:])) + ")"


def canonical(eq):
    names = {x: "v" + str(i) for i, x in enumerate(sorted(variables(eq[0]) | variables(eq[1])))}

    def walk(t):
        return names[t] if isinstance(t, str) else (t[0], *(walk(u) for u in t[1:]))

    return tuple(map(walk, eq))


def baseline713():
    rho = lambda x, y: T("p_eps", T("P", y, T("P", x, "b")), T("V", "b", D))
    rel = lambda x, y: T("p_E", x, y)
    h = T("Target", "b")
    nxt = lambda z: T("Next", "b", z)
    mem = lambda z: T("Mem", "b", z)
    r, e, f = rho(h, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z")
    a, b, c = rel(T("W", "x", D), "x"), rel("x", h), rho("x", "y")
    u, v = rel("y", h), rho(nxt("y"), "y")
    lower = meet(c, N(a, neg(b)))
    not_bad = N(r, meet(e, neg(f)))
    not_hull = N(N(lower, neg(u)), N(u, neg(v)))
    eqs = [
        (N(N("x", N(N("y", "x"), "x")), N("y", N("z", "x"))), "y"),
        (D, N(D, N(D, D))),
        (T("V", T("P", "x", "s"), D), "x"),
        (T("V", T("P", "x", "s"), T("A", "j", D)), T("V", "s", "j")),
        (T("p_eps", "s", T("P", "a", "b")), N(T("p_eps", "s", "a"), T("p_eps", "s", "b"))),
        (T("p_eps", "s", T("A", "i", "j")), rel(T("V", "s", "i"), T("V", "s", "j"))),
        (T("p_eps", "s", T("Q", "a")),
         N(T("p_eps", T("P", T("W", "s", "a"), "s"), "a"),
           T("p_eps", T("P", "z", "s"), "a"))),
        (D, N(not_bad, not_hull)),
    ]
    arities = {"d": 0, "N": 2, "V": 2, "P": 2, "A": 2, "Q": 1,
               "W": 2, "Target": 1, "Next": 2, "Mem": 2, "p_E": 2, "p_eps": 2}
    return {"name": "E713", "signature": arities, "equations": eqs,
            "start": N(D, D), "target": D, "binder_semantics": "exists-not"}


def specialize(data):
    def walk(t):
        return t if isinstance(t, str) else (ALIASES.get(t[0], t[0]), *(walk(u) for u in t[1:]))

    return {"name": "E704",
            "signature": {f: a for f, a in data["signature"].items() if f not in ALIASES},
            "equations": [tuple(map(walk, eq)) for eq in data["equations"]],
            "start": walk(data["start"]), "target": walk(data["target"]),
            "binder_semantics": "exists-not", "structural_witness_aliases": ALIASES,
            "status": "complete equational packet; ordinary relative model proof; no TM state count"}


def optimize_mux(data):
    """Replace the interval form of Hull by its Boolean multiplexer form."""
    rho = lambda x, y: T("p_eps", T("P", y, T("P", x, "b")), T("V", "b", D))
    rel = lambda x, y: T("p_E", x, y)
    h = T("Q", "b")
    nxt = lambda z: T("P", "b", z)
    mem = lambda z: T("A", "b", z)
    r, e, f = rho(h, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z")
    a, b, c = rel(T("W", "x", D), "x"), rel("x", h), rho("x", "y")
    u, v = rel("y", h), rho(nxt("y"), "y")
    not_lower = N(c, N(a, neg(b)))
    hull = N(N(neg(u), not_lower), N(u, v))
    not_bad = N(r, meet(e, neg(f)))
    eqs = data["equations"][:7] + [(D, N(not_bad, neg(hull)))]
    return {**data, "name": "E696", "equations": eqs,
            "boolean_optimization": "Hull=(not u and not lower) or (u and v), using not-lower directly"}


def optimize_selector(data):
    """Use existing unary Q as selector successor as well as class binder."""
    eqs = data["equations"].copy()
    assert eqs[3] == (T("V", T("P", "x", "s"), T("A", "j", D)), T("V", "s", "j"))
    eqs[3] = (T("V", T("P", "x", "s"), T("Q", "j")), T("V", "s", "j"))
    return {**data, "name": "E692", "equations": eqs,
            "selector_optimization": "zero=d; successor(i)=Q(i), with Q retaining its binder and raw Target roles"}


def encode(data):
    eqs = list(map(canonical, data["equations"]))
    cap = max(len(variables(a) | variables(b)) for a, b in eqs)
    syms = list(data["signature"])
    width = max(1, (cap + len(syms) - 1).bit_length())

    def term(t):
        if isinstance(t, str):
            return format(int(t[1:]), f"0{width}b")
        assert t[0] in data["signature"] and len(t) - 1 == data["signature"][t[0]]
        return format(cap + syms.index(t[0]), f"0{width}b") + "".join(term(u) for u in t[1:])

    header = format(len(syms), "08b") + "".join(format(data["signature"][f], "03b") for f in syms) + format(cap, "08b")
    equations = "".join("1" + term(a) + term(b) for a, b in eqs) + "0"
    endpoints = term(data["start"]) + term(data["target"])
    bits = header + equations + endpoints
    return bits, {"signature_symbols": len(syms), "variable_capacity": cap,
                  "opcode_width": width, "equations": len(eqs),
                  "equation_node_counts": [nodes(a) + nodes(b) for a, b in eqs],
                  "equation_nodes": sum(nodes(a) + nodes(b) for a, b in eqs),
                  "header_bits": len(header), "equation_bits": len(equations),
                  "endpoint_bits": len(endpoints), "complete_packet_bits": len(bits),
                  "bits_sha256": hashlib.sha256(bits.encode()).hexdigest()}


def decode(bits):
    position = 0

    def read(n):
        nonlocal position
        word = bits[position:position + n]
        if len(word) != n or any(c not in "01" for c in word):
            raise ValueError("bad or truncated field")
        position += n
        return int(word, 2)

    count = read(8)
    arities = [read(3) for _ in range(count)]
    cap = read(8)
    width = max(1, (cap + count - 1).bit_length())

    def term():
        code = read(width)
        if code < cap:
            return "v" + str(code)
        if code >= cap + count:
            raise ValueError("unused opcode")
        return (code - cap, *(term() for _ in range(arities[code - cap])))

    eqs = []
    while read(1):
        eqs.append((term(), term()))
    left, right = term(), term()
    if position != len(bits) or variables(left) or variables(right):
        raise ValueError("trailing input or nonground endpoint")
    return arities, cap, eqs, left, right


def verify(data, bits, metrics):
    syms = list(data["signature"])

    def erase(t):
        return t if isinstance(t, str) else (syms.index(t[0]), *(erase(u) for u in t[1:]))

    expected = (list(data["signature"].values()), metrics["variable_capacity"],
                [tuple(erase(t) for t in canonical(eq)) for eq in data["equations"]],
                erase(data["start"]), erase(data["target"]))
    assert decode(bits) == expected
    rejects = 0
    for bad in [bits[:i] for i in range(len(bits))] + [bits + "0", bits[:-1] + "x"]:
        try:
            decode(bad)
        except ValueError:
            rejects += 1
        else:
            raise AssertionError("accepted malformed encoding")
    return {"roundtrip": True, "strict_prefixes_rejected": len(bits), "other_rejections": rejects - len(bits)}


def boolean_checks():
    n = lambda x, y: not (x and y)
    total = 0
    for r, e, f, a, b, c, u, v in itertools.product((False, True), repeat=8):
        lower = c and (not a or b)
        rhs = n(n(r, e and not f), n(n(lower, not u), n(u, not v)))
        clauses = (r and e and not f) or ((a or not c or u) and (not b or not c or u) and (not u or v))
        assert rhs == clauses
        not_lower = n(c, n(a, n(True, b)))
        mux_hull = n(n(n(True, u), not_lower), n(u, v))
        mux_rhs = n(n(r, e and not f), n(True, mux_hull))
        assert mux_hull == ((not lower or u) and (not u or v))
        assert mux_rhs == rhs == clauses
        total += 1
    return total


def selector_checks():
    # Finite native-stack regressions, not a finite model of EPSC.
    leaves = [D, ("e0",), ("e1",)]
    domain = leaves + [T("Q", a) for a in leaves]
    domain += [T(f, a, b) for f in ("P", "A") for a in leaves for b in leaves]
    def value(s, i):
        k = 0
        while i[0] == "Q":
            k += 1
            i = i[1]
        for _ in range(k):
            if s[0] != "P":
                return D
            s = s[2]
        return s[1] if s[0] == "P" else D
    checks = 0
    for x, s in itertools.product(domain, repeat=2):
        assert value(T("P", x, s), D) == x
        checks += 1
        for j in domain:
            assert value(T("P", x, s), T("Q", j)) == value(s, j)
            checks += 1
    return checks


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    p.add_argument("--baseline", type=Path, help="optional literal incoming E713.bits for byte comparison")
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    baseline = baseline713()
    oldbits, oldmetrics = encode(baseline)
    assert oldmetrics["complete_packet_bits"] == 713
    assert oldmetrics["bits_sha256"] == "3cd0c3d0fb8d8640cfef1f44e0c22d377dd930de88a94093a2ef7650e22c9e72"
    if args.baseline:
        assert args.baseline.read_text().strip() == oldbits
    new = specialize(baseline)
    bits, metrics = encode(new)
    assert metrics["complete_packet_bits"] == 704
    assert metrics["equation_node_counts"] == [14, 6, 6, 10, 12, 12, 17, 82]
    assert metrics["equation_nodes"] == oldmetrics["equation_nodes"] == 159
    final = optimize_mux(new)
    finalbits, finalmetrics = encode(final)
    assert finalmetrics["complete_packet_bits"] == 696
    assert finalmetrics["equation_node_counts"] == [14, 6, 6, 10, 12, 12, 17, 80]
    assert finalmetrics["equation_nodes"] == 157
    primary = optimize_selector(final)
    primarybits, primarymetrics = encode(primary)
    assert primarymetrics["complete_packet_bits"] == 692
    assert primarymetrics["equation_node_counts"] == [14, 6, 6, 9, 12, 12, 17, 80]
    assert primarymetrics["equation_nodes"] == 156
    receipt = {"status": "PASS", "baseline713": oldmetrics, "combined704": metrics,
               "optimized696": finalmetrics,
               "unary_selector692": primarymetrics,
               "baseline_literal_compared": bool(args.baseline),
               "codec_checks704": verify(new, bits, metrics),
               "codec_checks696": verify(final, finalbits, finalmetrics),
               "codec_checks692": verify(primary, primarybits, primarymetrics),
               "boolean_assignments": boolean_checks(),
               "mux_equivalence_assignments": 256,
               "native_selector_regressions": selector_checks(),
               "scope": "Exact syntax, charged codec and Boolean transcription. The unbounded model proof is mathematical; no finite model of EPSC or TM compiler is claimed."}
    for data, outbits, outmetrics in [(new, bits, metrics), (final, finalbits, finalmetrics), (primary, primarybits, primarymetrics)]:
        name = data["name"]
        pad = (-len(outbits)) % 8
        packed = outbits + "0" * pad
        outmetrics = {**outmetrics, "packed_bytes": len(packed) // 8, "trailing_padding_bits": pad}
        (args.out / (name + ".bits")).write_text(outbits + "\n")
        (args.out / (name + ".bin")).write_bytes(int(packed, 2).to_bytes(len(packed) // 8, "big"))
        (args.out / (name + ".bitlength")).write_text(str(len(outbits)) + "\n")
        unpacked = "".join(format(b, "08b") for b in (args.out / (name + ".bin")).read_bytes())
        assert unpacked[:len(outbits)] == outbits and unpacked[len(outbits):] == "0" * pad
        assert decode(unpacked[:int((args.out / (name + ".bitlength")).read_text())]) == decode(outbits)
        (args.out / (name + ".json")).write_text(json.dumps({**data, "metrics": outmetrics}, indent=2) + "\n")
        (args.out / (name + ".equations")).write_text("\n".join(f"{pretty(a)} = {pretty(b)}" for a, b in data["equations"]) + "\nQUERY: " + pretty(data["start"]) + " = " + pretty(data["target"]) + "\n")
    (args.out / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
