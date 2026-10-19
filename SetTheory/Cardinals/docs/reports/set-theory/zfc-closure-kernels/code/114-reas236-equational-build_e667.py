#!/usr/bin/env python3
"""Delete the redundant top equation from the exact inherited E692 packet.

No binary Turing-machine count is claimed. The exact mathematical argument
is in top_elimination.tex. Sh1's established Boolean-algebra interpretation
is an explicit prior theorem, not something inferred from a finite test.
The Boolean identity used by our new deduction is checked by exact Boolean
ring normalization. Only Python's standard library is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

INPUT_JSON_SHA = "0657cefef8f41bd7e463eb0adcd5a44b118de62ec852729202d3ecc4b6942d43"
INPUT_BITS_SHA = "0d05d8ee60cec00dc12b9f5b97a7567832a979829a7759f3b59e564ed8da974b"
PIN = "1b27f052d770f4c7d435e82e779bf21f5a1f66ed"


def freeze(t):
    return tuple(map(freeze, t)) if isinstance(t, list) else t


def T(f, *args):
    return (f, *args)


def N(a, b):
    return T("N", a, b)


D = T("d")


def variables(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(variables(a) for a in t[1:]))


def nodes(t):
    return 1 if isinstance(t, str) else 1 + sum(nodes(a) for a in t[1:])


def pretty(t):
    if isinstance(t, str):
        return t
    return t[0] if len(t) == 1 else t[0] + "(" + ",".join(pretty(a) for a in t[1:]) + ")"


def canonical(eq):
    vs = {v: "v" + str(i) for i, v in enumerate(sorted(variables(eq[0]) | variables(eq[1])))}
    def walk(t):
        return vs[t] if isinstance(t, str) else T(t[0], *(walk(a) for a in t[1:]))
    return tuple(map(walk, eq))


def encode(packet):
    arities = packet["signature"]
    symbols = list(arities)
    equations = [canonical(e) for e in packet["equations"]]
    capacity = max(len(variables(a) | variables(b)) for a, b in equations)
    width = max(1, (len(symbols) + capacity - 1).bit_length())
    def term(t):
        if isinstance(t, str):
            return format(int(t[1:]), f"0{width}b")
        assert len(t) - 1 == arities[t[0]]
        return format(capacity + symbols.index(t[0]), f"0{width}b") + "".join(term(a) for a in t[1:])
    header = format(len(symbols), "08b") + "".join(format(arities[s], "03b") for s in symbols) + format(capacity, "08b")
    body = "".join("1" + term(a) + term(b) for a, b in equations) + "0"
    endpoints = term(packet["start"]) + term(packet["target"])
    bits = header + body + endpoints
    return bits, {
        "signature_symbols": len(symbols), "variable_capacity": capacity,
        "opcode_width": width, "equations": len(equations),
        "equation_node_counts": [nodes(a) + nodes(b) for a, b in equations],
        "equation_nodes": sum(nodes(a) + nodes(b) for a, b in equations),
        "header_bits": len(header), "equation_bits": len(body),
        "endpoint_bits": len(endpoints), "complete_packet_bits": len(bits),
        "packed_bytes": (len(bits) + 7) // 8, "trailing_padding_bits": -len(bits) % 8,
        "logical_bits_sha256": hashlib.sha256(bits.encode()).hexdigest(),
    }


def decode(bits):
    pos = 0
    def read(n):
        nonlocal pos
        s = bits[pos:pos+n]
        if len(s) != n or any(c not in "01" for c in s):
            raise ValueError("malformed or truncated field")
        pos += n
        return int(s, 2)
    count = read(8)
    arities = [read(3) for _ in range(count)]
    cap = read(8)
    width = max(1, (count + cap - 1).bit_length())
    def term():
        tag = read(width)
        if tag < cap:
            return "v" + str(tag)
        if tag >= cap + count:
            raise ValueError("unused opcode")
        return (tag-cap, *(term() for _ in range(arities[tag-cap])))
    eqs = []
    while read(1):
        eqs.append((term(), term()))
    start, target = term(), term()
    if pos != len(bits) or variables(start) or variables(target):
        raise ValueError("trailing data or nonground endpoint")
    return arities, cap, eqs, start, target


def verify_codec(packet, bits, metrics):
    symbols = list(packet["signature"])
    def erase(t):
        return t if isinstance(t, str) else (symbols.index(t[0]), *(erase(a) for a in t[1:]))
    expected = (
        list(packet["signature"].values()), metrics["variable_capacity"],
        [tuple(erase(t) for t in canonical(e)) for e in packet["equations"]],
        erase(packet["start"]), erase(packet["target"]),
    )
    assert decode(bits) == expected
    for truncated in (bits[:n] for n in range(len(bits))):
        try:
            decode(truncated)
        except ValueError:
            pass
        else:
            raise AssertionError("strict prefix accepted")
    for malformed in (bits + "0", bits[:-1] + "x"):
        try:
            decode(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("malformed string accepted")
    return {"exact_roundtrip": True, "strict_prefixes_rejected": len(bits), "other_rejections": 2}


# A polynomial is the set of its nonzero squarefree monomials over F_2.
# Symmetric difference adds coefficients; union multiplies monomials.
# These operations are justified in every Boolean ring, irrespective of
# the number of elements. This is symbolic normalization, not a sample.
ONE = {frozenset()}


def pmul(p, q):
    result = set()
    for a in p:
        for b in q:
            m = a | b
            if m in result:
                result.remove(m)
            else:
                result.add(m)
    return result


def anf(t):
    if isinstance(t, str):
        return {frozenset([t])}
    assert t[0] == "N" and len(t) == 3
    return ONE ^ pmul(anf(t[1]), anf(t[2]))


def show_poly(p):
    return sorted([sorted(m) for m in p])


def proof_checks(e692):
    es = e692["equations"]
    assert len(es) == 8
    assert es[0] == (N(N("x", N(N("y", "x"), "x")), N("y", N("z", "x"))), "y")
    assert es[1] == (D, N(D, N(D, D)))
    assert es[2] == (T("V", T("P", "x", "s"), D), "x")
    assert es[3] == (T("V", T("P", "x", "s"), T("Q", "j")), T("V", "s", "j"))
    assert es[4] == (T("p_eps", "s", T("P", "a", "b")), N(T("p_eps", "s", "a"), T("p_eps", "s", "b")))
    left, right = es[7]
    assert left == D and right[0] == "N"
    nr, dh = right[1:]
    assert nr[0] == "N" and nr[2][0:2] == ("N", D)
    assert dh[0:2] == ("N", D)
    r = nr[1]
    expected_r = T("p_eps", T("P", T("P", "b", "z"), T("P", T("Q", "b"), "b")), T("V", "b", D))
    assert r == expected_r
    # A tautological class exists without requiring d to denote truth.
    tau = N("u", N("u", "u"))
    assert anf(tau) == ONE
    # Let F=N(N(tau(u),N(d,k)),N(d,h)). The crucial equational
    # identity N(F,N(d,d))=d holds for all Boolean algebras.
    F = N(N(tau, N("d", "k")), N("d", "h"))
    lhs = N(F, N("d", "d"))
    assert anf(lhs) == anf("d")
    # Ground descriptor used to instantiate the inherited closure row.
    cls = T("P", D, T("P", D, D))
    descriptor = T("P", cls, D)
    return {
        "inherited_equations_identified": True,
        "deleted_equation_index_zero_based": 1,
        "retained_closure_pattern": "d=N(N(r,N(d,k)),N(d,h))",
        "literal_r_identified": True,
        "tautological_class": pretty(cls),
        "descriptor": pretty(descriptor),
        "endpoint_collapse_chain": [
            "x", "V(P(x,P(y,d)),d)", "V(P(x,P(y,d)),Q(d))",
            "V(P(y,d),d)", "y",
        ],
        "truth_term": pretty(tau),
        "truth_term_anf": show_poly(anf(tau)),
        "boolean_identity_lhs": pretty(lhs),
        "boolean_identity_rhs": "d",
        "boolean_identity_lhs_anf": show_poly(anf(lhs)),
        "boolean_identity_rhs_anf": show_poly(anf("d")),
        "proof_scope": "Exact Boolean ring identity plus literal source-row checks. Sh1-to-Boolean-algebra uses the cited published theorem; no full proof-assistant endpoint.",
    }


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O/-OO; verification assertions are required.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=Path(__file__).resolve().parent / "inputs")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent / "generated")
    args = parser.parse_args()
    src_json = args.input_dir / "E692.json"
    src_bits = args.input_dir / "E692.bits"
    assert hashlib.sha256(src_json.read_bytes()).hexdigest() == INPUT_JSON_SHA
    assert hashlib.sha256(src_bits.read_bytes()).hexdigest() == INPUT_BITS_SHA
    base = json.loads(src_json.read_text())
    base["equations"] = [freeze(e) for e in base["equations"]]
    base["start"], base["target"] = freeze(base["start"]), freeze(base["target"])
    oldbits, oldmetrics = encode(base)
    assert oldbits == src_bits.read_text().strip()
    assert len(oldbits) == 692
    proof = proof_checks(base)
    new = {
        "name": "E667", "signature": base["signature"],
        "equations": base["equations"][:1] + base["equations"][2:],
        "start": base["start"], "target": base["target"],
        "status": "Exact same equational theory as E692 by the ordinary top-elimination proof; no binary Turing-machine count.",
        "provenance": {"repository": "https://github.com/VladimirReshetnikov/ProveIt", "commit": PIN,
            "archive": "docs/incoming/ZFC_Sub237_Research_2026-10-19.zip",
            "member": "zfc_sub237_research_20261019/equational/generated/E692.json",
            "raw_json_sha256": INPUT_JSON_SHA, "raw_bits_sha256": INPUT_BITS_SHA},
    }
    bits, metrics = encode(new)
    assert metrics["complete_packet_bits"] == 667
    assert metrics["equations"] == 7 and metrics["equation_nodes"] == 150
    check = verify_codec(new, bits, metrics)
    args.output.mkdir(parents=True, exist_ok=True)
    new["metrics"] = metrics
    (args.output / "E667.json").write_text(json.dumps(new, indent=2) + "\n")
    (args.output / "E667.bits").write_text(bits + "\n")
    padding = -len(bits) % 8
    (args.output / "E667.bin").write_bytes(int(bits + "0" * padding, 2).to_bytes((len(bits) + 7) // 8, "big"))
    (args.output / "E667.bitlength").write_text(str(len(bits)) + "\n")
    text = "\n".join(pretty(a) + " = " + pretty(b) for a, b in new["equations"])
    text += "\nQUERY: " + pretty(new["start"]) + " = " + pretty(new["target"]) + "\n"
    (args.output / "E667.equations").write_text(text)
    receipt = {"status": "PASS", "baseline_metrics": oldmetrics, "new_metrics": metrics,
               "new_proof_checks": proof, "codec_checks": check,
               "saving": {"equations": 1, "term_nodes": 6, "logical_bits": 25},
               "binary_tm_state_count": None}
    (args.output / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "packet": "E667", **metrics}, sort_keys=True))
    # A second, independent reduction of the designated ground query.
    query_packet = {**new, "name": "E663", "start": T("Q", D), "target": D,
                    "query_equivalence": "Q(d)=d iff the native stack algebra collapses iff N(d,d)=d under Sh1; endpoint_shortening.tex"}
    qbits, qmetrics = encode(query_packet)
    assert len(qbits) == 663 and qmetrics["equation_nodes"] == 150
    qcheck = verify_codec(query_packet, qbits, qmetrics)
    query_packet["metrics"] = qmetrics
    (args.output / "E663.json").write_text(json.dumps(query_packet, indent=2) + "\n")
    (args.output / "E663.bits").write_text(qbits + "\n")
    padding = -len(qbits) % 8
    (args.output / "E663.bin").write_bytes(int(qbits + "0" * padding, 2).to_bytes((len(qbits) + 7) // 8, "big"))
    (args.output / "E663.bitlength").write_text(str(len(qbits)) + "\n")
    qtext = "\n".join(pretty(a) + " = " + pretty(b) for a, b in query_packet["equations"])
    qtext += "\nQUERY: " + pretty(query_packet["start"]) + " = " + pretty(query_packet["target"]) + "\n"
    (args.output / "E663.equations").write_text(qtext)
    (args.output / "verification_E663.json").write_text(json.dumps({
        "status": "PASS", "metrics": qmetrics, "codec_checks": qcheck,
        "same_equations_and_signature_as_E667": True, "endpoint_node_saving": 1,
        "endpoint_bit_saving": 4, "binary_tm_state_count": None,
        "endpoint_collapse_chain": proof["endpoint_collapse_chain"],
    }, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "packet": "E663", **qmetrics}, sort_keys=True))


if __name__ == "__main__":
    main()
