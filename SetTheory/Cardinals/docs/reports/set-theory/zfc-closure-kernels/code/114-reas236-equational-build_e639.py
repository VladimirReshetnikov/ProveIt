#!/usr/bin/env python3
"""Build the self-descriptor E639 consistency packet, with E668/E643 controls.

The only new clause-level representation change is replacing the three
occurrences V(b,d) in the closure equation by b. The proof of its calibration
is self_descriptor.tex. The equation change is a relative model theorem,
not an assertion that old and new closure clauses have identical models.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from build_e667 import (
    D, INPUT_JSON_SHA, INPUT_BITS_SHA, PIN, ONE, N, T, anf, encode,
    freeze, pretty, proof_checks, show_poly, verify_codec,
)


def change_descriptor(eqs):
    needle = T("V", "b", D)
    changed = 0
    def walk(t):
        nonlocal changed
        if t == needle:
            changed += 1
            return "b"
        return t if isinstance(t, str) else T(t[0], *(walk(a) for a in t[1:]))
    new = eqs[:-1] + [tuple(walk(t) for t in eqs[-1])]
    assert changed == 3
    assert new[:-1] == eqs[:-1]
    return new, changed


def extra_checks(eqs):
    # ANF validates the protected-parameter-tail identity in every Boolean
    # algebra. t is a tautological class, f a contradictory class.
    tau = N("u", N("u", "u"))
    false = N(tau, tau)
    true_tail = N(false, "parameters")
    self_descriptor = N("code", true_tail)
    assert anf(false) == set()
    assert anf(true_tail) == ONE
    assert anf(self_descriptor) == anf(N("code", "code"))
    # Literal closure still has the form required for truth elimination.
    left, right = eqs[-1]
    assert left == D and right[0] == "N"
    nr, dh = right[1:]
    assert nr[0] == "N" and nr[2][0:2] == ("N", D)
    assert dh[0:2] == ("N", D)
    expected_r = T("p_eps", T("P", T("P", "b", "z"), T("P", T("Q", "b"), "b")), "b")
    assert nr[1] == expected_r
    # Coordinates of a protected descriptor, independent of the algebraic
    # meaning of any data parameter. This is a finite symbolic stack check;
    # the all-length proof follows by the retained head/tail equations.
    cls_true = T("P", D, T("P", D, D))
    cls_false = T("P", cls_true, cls_true)
    def cons(values, tail=D):
        for value in reversed(values):
            tail = T("P", value, tail)
        return tail
    def coordinate(s, k):
        for _ in range(k):
            assert s[0] == "P"
            s = s[2]
        assert s[0] == "P"
        return s[1]
    coordinate_checks = 0
    for length in range(65):
        params = [f"p{i}" for i in range(length)]
        data = cons(params)
        b = T("P", "code", T("P", cls_false, data))
        stream = T("P", "output", T("P", "input", b))
        expected = ["output", "input", "code", cls_false, *params]
        for i, value in enumerate(expected):
            assert coordinate(stream, i) == value
            coordinate_checks += 1
    return {
        "three_literal_code_projection_replacements": True,
        "protected_false_class": pretty(cls_false),
        "protected_descriptor": "P(code,P(false_class,parameter_list))",
        "descriptor_anf": show_poly(anf(self_descriptor)),
        "complement_code_anf": show_poly(anf(N("code", "code"))),
        "uniform_true_tail_anf": show_poly(anf(true_tail)),
        "literal_new_closure_pattern_checked": True,
        "finite_symbolic_coordinate_checks": coordinate_checks,
        "coordinate_lengths": [0, 64],
        "mathematical_scope": "Boolean identities exact for all Boolean algebras; finite stack checks support the stated all-length head/tail induction; consistency calibration is the ordinary model proof in self_descriptor.tex.",
    }


def emit(packet, output):
    bits, metrics = encode(packet)
    check = verify_codec(packet, bits, metrics)
    packet["metrics"] = metrics
    name = packet["name"]
    (output / (name + ".json")).write_text(json.dumps(packet, indent=2) + "\n")
    (output / (name + ".bits")).write_text(bits + "\n")
    (output / (name + ".bitlength")).write_text(str(len(bits)) + "\n")
    padding = -len(bits) % 8
    (output / (name + ".bin")).write_bytes(int(bits + "0" * padding, 2).to_bytes((len(bits) + 7) // 8, "big"))
    txt = "\n".join(pretty(a) + " = " + pretty(b) for a, b in packet["equations"])
    txt += "\nQUERY: " + pretty(packet["start"]) + " = " + pretty(packet["target"]) + "\n"
    (output / (name + ".equations")).write_text(txt)
    return metrics, check


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O/-OO; verification assertions are required.")
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent
    parser.add_argument("--input-dir", type=Path, default=root / "inputs")
    parser.add_argument("--output", type=Path, default=root / "generated")
    args = parser.parse_args()
    p = args.input_dir / "E692.json"
    bp = args.input_dir / "E692.bits"
    assert hashlib.sha256(p.read_bytes()).hexdigest() == INPUT_JSON_SHA
    assert hashlib.sha256(bp.read_bytes()).hexdigest() == INPUT_BITS_SHA
    base = json.loads(p.read_text())
    base["equations"] = [freeze(e) for e in base["equations"]]
    base["start"], base["target"] = freeze(base["start"]), freeze(base["target"])
    baseline_bits, _ = encode(base)
    assert baseline_bits == bp.read_text().strip()
    proof_checks(base)
    eqs, changes = change_descriptor(base["equations"])
    new_checks = extra_checks(eqs)
    common = {
        "signature": base["signature"], "equations": eqs,
        "start": base["start"], "target": base["target"],
        "status": "Finite equational packet with ordinary relative calibration to E692/raw EPSC; no binary TM state count.",
        "provenance": {"repository": "https://github.com/VladimirReshetnikov/ProveIt", "commit": PIN,
            "archive": "docs/incoming/ZFC_Sub237_Research_2026-10-19.zip",
            "member": "zfc_sub237_research_20261019/equational/generated/E692.json",
            "raw_json_sha256": INPUT_JSON_SHA, "raw_bits_sha256": INPUT_BITS_SHA},
        "descriptor_change": "R_b(x,y)=p_eps(P(y,P(x,b)),b); protected true parameter tail gives arbitrary formula/parameter coverage.",
    }
    packets = [
        {**common, "name": "E668"},
        {**common, "name": "E643", "equations": eqs[:1] + eqs[2:]},
        {**common, "name": "E639", "equations": eqs[:1] + eqs[2:], "start": T("Q", D)},
    ]
    expected = {"E668": (668, 150, 8), "E643": (643, 144, 7), "E639": (639, 144, 7)}
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for packet in packets:
        metrics, checks = emit(packet, args.output)
        assert (metrics["complete_packet_bits"], metrics["equation_nodes"], metrics["equations"]) == expected[packet["name"]]
        results.append({"name": packet["name"], "metrics": metrics, "codec_checks": checks})
        print(json.dumps({"status": "PASS", "packet": packet["name"], **metrics}, sort_keys=True))
    receipt = {"status": "PASS", "results": results, "new_checks": new_checks,
        "descriptor_replacements": changes, "descriptor_term_node_saving": 6,
        "truth_equation_node_saving": 6, "truth_equation_marker_saving": 1,
        "query_node_saving": 1, "total_bit_saving_against_E692": 53,
        "binary_tm_state_count": None,
        "proof_scope": "Ordinary model proof and exact symbolic/codec checks; no Lean/Rocq endpoint."}
    (args.output / "verification_E639.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
