#!/usr/bin/env python3
"""Complete EPSC equational packets with a complemented existential binder.

This file emits *all* equations, arities, variable capacity and endpoints.
It does not generate a Turing machine. The mathematical calibration is in
kernel_note.tex. Terms are tuples (function, arguments...) and variable strings.
The Source79/946 signature, stack, Boolean basis and packet codec are inherited;
the source/provenance notes list the dependencies and their limited status.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

D = ("d",)


def t(f, *args): return (f, *args)
def n(a, b): return t("N", a, b)
def neg(a): return n(D, a)
def meet(a, b): return neg(n(a, b))
def join(a, b): return n(neg(a), neg(b))
def nodes(a): return 1 if isinstance(a, str) else 1 + sum(map(nodes, a[1:]))
def variables(a):
    return {a} if isinstance(a, str) else set().union(*(variables(x) for x in a[1:]))


def pretty(a):
    if isinstance(a, str): return a
    return a[0] if len(a) == 1 else a[0] + "(" + ",".join(map(pretty, a[1:])) + ")"


def canonical(eq):
    names = sorted(variables(eq[0]) | variables(eq[1]))
    names = {name: "v" + str(i) for i, name in enumerate(names)}
    def go(a):
        return names[a] if isinstance(a, str) else (a[0], *(go(x) for x in a[1:]))
    return tuple(map(go, eq))


def build(variant="713"):
    # Every displayed abbreviation below is expanded before encoding.
    h = t("Target", "b")
    nxt = lambda z: t("Next", "b", z)
    mem = lambda z: t("Mem", "b", z)
    rho = lambda x, y: t("p_eps", t("P", y, t("P", x, "b")), t("V", "b", D))
    rel = lambda x, y: t("p_E", x, y)
    quantified = t("p_eps", "s", t("Q", "a"))
    selected = t("p_eps", t("P", t("W", "s", "a"), "s"), "a")
    arbitrary = t("p_eps", t("P", "z", "s"), "a")
    guard = t("p_G", "b")

    # Bad local-boundedness branch: r & e & ~f.
    r, e, f = rho(h, nxt("z")), rel(mem("z"), nxt("z")), rel(mem("z"), "z")
    # Hull branch: (a | ~c | d) & (~b | ~c | d) & (~d | s).
    aa = rel(t("W", "x", D), "x")
    bb, cc, dd, ss = rel("x", h), rho("x", "y"), rel("y", h), rho(nxt("y"), "y")
    lower = meet(cc, n(aa, neg(bb)))
    not_bad = n(r, meet(e, neg(f)))
    not_hull = n(n(lower, neg(dd)), n(dd, neg(ss)))

    equations = [
        (n(n("x", n(n("y", "x"), "x")), n("y", n("z", "x"))), "y"),
        (D, n(D, n(D, D))),
        (t("V", t("P", "x", "s"), D), "x"),
        (t("V", t("P", "x", "s"), t("A", "j", D)), t("V", "s", "j")),
        (t("p_eps", "s", t("P", "a", "b")), n(t("p_eps", "s", "a"), t("p_eps", "s", "b"))),
        (t("p_eps", "s", t("A", "i", "j")), rel(t("V", "s", "i"), t("V", "s", "j"))),
    ]
    if variant == "946":
        # Original (ordinary existential) witness equality and upper bound.
        equations.extend([(quantified, selected), (D, n(arbitrary, neg(quantified)))])
    else:
        # New Q means exists-not, and W selects a falsifying instance.
        equations.append((quantified, n(selected, arbitrary)))

    if variant in ("946", "917"):
        equations.extend([
            (D, n(neg(guard), neg(r))),
            (D, n(neg(guard), neg(e))),
            (D, n(neg(guard), f)),
            (D, n(guard, meet(neg(aa), meet(cc, neg(dd))))),
            (D, n(guard, meet(bb, meet(cc, neg(dd))))),
            (D, n(guard, meet(dd, neg(ss)))),
        ])
    elif variant == "745":
        equations.extend([
            (D, n(neg(guard), not_bad)),
            # Under guard: lower <= dd <= ss. The complement of lower
            # simplifies to N(cc,N(aa,N(d,bb))) without a double negation.
            (n(guard, n(n(cc, n(aa, neg(bb))), neg(dd))), n(guard, meet(dd, ss))),
        ])
    elif variant == "713":
        equations.append((D, n(not_bad, not_hull)))
    else:
        raise ValueError(variant)

    order = ["d", "N", "V", "P", "A", "Q", "W", "Target", "Next", "Mem", "p_E", "p_eps", "p_G"]
    signature = {}
    def visit(a):
        if isinstance(a, str): return
        if a[0] in signature: assert signature[a[0]] == len(a) - 1
        signature[a[0]] = len(a) - 1
        for child in a[1:]: visit(child)
    for eq in equations:
        for side in eq: visit(side)
    return {"name": "E" + variant, "equations": equations,
            "signature": {k: signature[k] for k in order if k in signature},
            "start": n(D, D), "target": D,
            "binder_semantics": "exists" if variant == "946" else "exists-not",
            "status": "complete equational consistency packet; no Turing-machine state count"}


def encode(data):
    equations = list(map(canonical, data["equations"]))
    capacity = max(len(variables(a) | variables(b)) for a, b in equations)
    symbols = list(data["signature"])
    width = max(1, (capacity + len(symbols) - 1).bit_length())
    def term(a):
        if isinstance(a, str): return format(int(a[1:]), f"0{width}b")
        return format(capacity + symbols.index(a[0]), f"0{width}b") + "".join(term(x) for x in a[1:])
    header = format(len(symbols), "08b") + "".join(format(data["signature"][s], "03b") for s in symbols) + format(capacity, "08b")
    rules = "".join("1" + term(a) + term(b) for a, b in equations) + "0"
    endpoints = term(data["start"]) + term(data["target"])
    bits = header + rules + endpoints
    metrics = {"signature_symbols": len(symbols), "variable_capacity": capacity,
               "opcode_width": width, "equations": len(equations),
               "both_side_tree_nodes": sum(nodes(a) + nodes(b) for a, b in equations),
               "header_bits": len(header), "equation_bits": len(rules),
               "endpoint_bits": len(endpoints), "complete_packet_bits": len(bits),
               "bits_sha256": hashlib.sha256(bits.encode()).hexdigest()}
    return bits, metrics


def decode(bits):
    pos = 0
    def read(width):
        nonlocal pos
        word = bits[pos:pos+width]
        if len(word) != width or any(c not in "01" for c in word): raise ValueError("invalid field")
        pos += width
        return int(word, 2)
    count = read(8)
    arities = [read(3) for _ in range(count)]
    capacity = read(8)
    width = max(1, (count + capacity - 1).bit_length())
    def term():
        tag = read(width)
        if tag < capacity: return "v" + str(tag)
        if tag >= capacity + count: raise ValueError("unused opcode")
        return (tag - capacity, *(term() for _ in range(arities[tag - capacity])))
    equations = []
    while read(1): equations.append((term(), term()))
    start, target = term(), term()
    if pos != len(bits): raise ValueError("trailing input")
    if variables(start) | variables(target): raise ValueError("nonground target")
    return arities, capacity, equations, start, target


def verify_roundtrip(data):
    bits, metrics = encode(data)
    symbols = list(data["signature"])
    def erase(a): return a if isinstance(a, str) else (symbols.index(a[0]), *(erase(x) for x in a[1:]))
    expected = (list(data["signature"].values()), metrics["variable_capacity"],
                [tuple(erase(x) for x in canonical(eq)) for eq in data["equations"]],
                erase(data["start"]), erase(data["target"]))
    assert decode(bits) == expected
    for cut in range(len(bits)):
        try: decode(bits[:cut])
        except ValueError: pass
        else: raise AssertionError(("accepted truncated packet", cut))
    for malformed in [bits+"0", bits[:-1]+"x"]:
        try: decode(malformed)
        except ValueError: pass
        else: raise AssertionError("accepted malformed packet")
    metrics.update(strict_truncations_checked=len(bits), malformed_checks=2)
    return bits, metrics


def verify_boolean_factorings():
    checks = 0
    for r, e, f, a, b, c, d, s in itertools.product((False, True), repeat=8):
        nn = lambda u, v: not (u and v)
        bad = r and e and not f
        hull = (a or not c or d) and (not b or not c or d) and (not d or s)
        lower = c and (not a or b)
        not_bad = nn(r, e and not f)
        not_hull = nn(nn(lower, not d), nn(d, not s))
        assert nn(not_bad, not_hull) == (bad or hull)
        assert hull == ((lower or d) == (d and s))
        for g in (False, True):
            assert ((g or r) and (g or e) and (g or not f)) == (g or bad)
            assert ((not g or a or not c or d) and (not g or not b or not c or d) and (not g or not d or s)) == (not g or hull)
            assert (nn(g, lower or d) == nn(g, d and s)) == (not g or hull)
            checks += 1
    return checks


def verify_quantifier():
    # Power-set Boolean algebras; this is NOT a finite model of EPSC.
    checks = 0
    for atom_count in range(1, 4):
        top = (1 << atom_count) - 1
        nn = lambda a, b: top ^ (a & b)
        for length in range(1, 4):
            for values in itertools.product(range(top + 1), repeat=length):
                for picked in range(length):
                    w = values[picked]
                    for q in range(top + 1):
                        fused = all(q == nn(w, a) for a in values)
                        minimum = (q == (top ^ w) and all((w & a) == w for a in values))
                        assert fused == minimum
                        if atom_count == 1 and fused:
                            assert bool(q) == any(not bool(a) for a in values)
                            if q: assert not w
                        checks += 1
    return checks


def verify_flag_elimination():
    checks = 0
    for m in range(1, 5):
        for k in range(1, 5):
            for bad in itertools.product((False, True), repeat=m):
                for hull in itertools.product((False, True), repeat=k):
                    pointwise = all(a or b for a in bad for b in hull)
                    branches = any(all(g or a for a in bad) and all(not g or b for b in hull) for g in (False, True))
                    assert pointwise == branches
                    checks += 1
    return checks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "generated")
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    results = {"status": "finite transcription, Boolean algebra and codec checks only",
               "boolean_factoring_rows": verify_boolean_factorings(),
               "finite_Boolean_quantifier_rows": verify_quantifier(),
               "finite_flag_elimination_rows": verify_flag_elimination(), "variants": []}
    for name in ["946", "917", "745", "713"]:
        data = build(name)
        bits, metrics = verify_roundtrip(data)
        assert metrics["complete_packet_bits"] == int(name)
        data["metrics"] = metrics
        (args.out / (data["name"] + ".bits")).write_text(bits + "\n")
        (args.out / (data["name"] + ".json")).write_text(json.dumps(data, indent=2) + "\n")
        (args.out / (data["name"] + ".equations")).write_text("\n".join(f"{i}: {pretty(a)} = {pretty(b)}" for i, (a, b) in enumerate(data["equations"])) + "\n")
        results["variants"].append({"name": data["name"], **metrics})
    (args.out / "verification.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    if not __debug__: raise SystemExit("Run without -O; checks use assertions.")
    main()
