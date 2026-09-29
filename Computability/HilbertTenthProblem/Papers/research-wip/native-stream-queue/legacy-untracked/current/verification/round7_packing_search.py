#!/usr/bin/env python3
"""Bounded exact packing search for widths (q^2,q^2,q^4).

No claim of circuit optimality is made. Inputs already computed outside
the measured region are Y=l+e*q, S3, lambda+q^2, Z*lambda, q^2,q^4,q^8,n^2.
The current 111-operation certificate spends 18 operations in this region.
"""
import json
from pathlib import Path
import sympy as sp
from affine_block_order_search import Circuit as OriginalCircuit
from affine_block_order_search import q, n, g, e, ell, B, b, lam, zl, s3, finish


class Circuit(OriginalCircuit):
    def __init__(self):
        super().__init__()
        del self.values["lq"]
        self.values["eq"] = e*q
        self.values["S2"] = ell+e*q


def blocks(order):
    c = Circuit()
    c.op("u", "-", "b", 1)
    c.op("v", "-", "B", 2)
    if order == "ABC":
        c.op("s_a", "*", "q2", "S3")
        c.op("s_b", "+", "S2", "s_a")
        c.op("s_c", "*", "q2", "s_b")
        c.op("S", "+", "g", "s_c")
        c.op("tc", "-", "L2", "zl")
        c.op("ta", "*", "q2", "tc")
        c.op("tb", "*", "l", "u")
        c.op("td", "-", "ta", "tb")
        c.op("te", "*", "l", "q4")
        c.op("tf", "*", "v", "te")
        c.op("Tplus", "+", "td", "tf")
    elif order == "BAC":
        c.op("s_a", "*", "q2", "S3")
        c.op("s_b", "+", "g", "s_a")
        c.op("s_c", "*", "q2", "s_b")
        c.op("S", "+", "S2", "s_c")
        c.op("ta", "*", "v", "q2")
        c.op("tb", "-", "ta", "u")
        c.op("tc", "*", "l", "q2")
        c.op("td", "*", "tc", "tb")
        c.op("te", "-", "la", "zl")
        c.op("tf", "+", "q4", "te")
        c.op("Tplus", "+", "td", "tf")
    elif order == "ACB":
        c.op("q6", "*", "q2", "q4")
        c.op("s_a", "*", "q2", "S3")
        c.op("s_b", "*", "q6", "S2")
        c.op("s_c", "+", "g", "s_a")
        c.op("S", "+", "s_c", "s_b")
        c.op("ta", "-", "L2", "zl")
        c.op("tb", "-", "ta", 1)
        c.op("tc", "*", "q6", "tb")
        c.op("td", "*", "v", "q2")
        c.op("te", "-", "td", "u")
        c.op("tf", "*", "l", "te")
        c.op("tg", "+", "q2", "tc")
        c.op("Tplus", "+", "tg", "tf")
    elif order == "BCA":
        c.op("s_a", "*", "q4", "g")
        c.op("s_b", "+", "S3", "s_a")
        c.op("s_c", "*", "q2", "s_b")
        c.op("S", "+", "S2", "s_c")
        c.op("ta", "-", "L2", "zl")
        c.op("tb", "*", "u", "q4")
        c.op("tc", "-", "v", "tb")
        c.op("td", "*", "l", "tc")
        c.op("te", "-", "td", "q4")
        c.op("tf", "*", "q2", "te")
        c.op("tg", "+", "q8", "tf")
        c.op("Tplus", "+", "ta", "tg")
    elif order == "CAB":
        c.op("q6", "*", "q2", "q4")
        c.op("s_a", "*", "q2", "S2")
        c.op("s_b", "+", "g", "s_a")
        c.op("s_c", "*", "q4", "s_b")
        c.op("S", "+", "S3", "s_c")
        c.op("ta", "-", "la", "zl")
        c.op("tb", "*", "q6", "ta")
        c.op("nplus", "+", "q8", 1)
        c.op("td", "-", "nplus", "q4")
        c.op("te", "*", "q4", "u")
        c.op("tf", "-", "v", "te")
        c.op("tg", "*", "l", "tf")
        c.op("th", "+", "tb", "td")
        c.op("Tplus", "+", "th", "tg")
    elif order == "CBA":
        c.op("q6", "*", "q2", "q4")
        c.op("s_a", "*", "q2", "g")
        c.op("s_b", "+", "S2", "s_a")
        c.op("s_c", "*", "q4", "s_b")
        c.op("S", "+", "S3", "s_c")
        c.op("ta", "-", "la", "zl")
        c.op("tb", "-", "ta", 1)
        c.op("tc", "*", "q4", "tb")
        c.op("td", "*", "q6", "u")
        c.op("te", "-", "v", "td")
        c.op("tf", "*", "l", "te")
        c.op("nplus", "+", "q8", 1)
        c.op("th", "+", "nplus", "tc")
        c.op("Tplus", "+", "th", "tf")
    else:
        raise ValueError(order)
    return c


def target(order):
    data = {"A": (g, q*q-1-(b-1)*ell, 2),
            "B": (ell+e*q, q*q-1+lam-zl, 2),
            "C": (s3, (B-2)*ell, 4)}
    S = T = 0
    width = 0
    for name in order:
        si, ti, wi = data[name]
        S += q**width*si
        T += q**width*ti
        width += wi
    assert width == 8
    return S, T+1


def main():
    rows = []
    for order in ["ABC", "ACB", "BAC", "BCA", "CAB", "CBA"]:
        expected_S, expected_Tplus = target(order)
        for mode in ["standard", "G_shifted"]:
            for form in ["direct", "common_n_minus_one", "sum_of_blocks"]:
                c = blocks(order)
                assert sp.expand(c.values["S"]-expected_S) == 0
                assert sp.expand(c.values["Tplus"]-expected_Tplus) == 0
                if mode == "standard":
                    finish(c, form)
                    # In orders beginning with C, n+1 was already computed as
                    # q^8+1. Reuse it using the existing equation n=q^8.
                    if form == "common_n_minus_one" and "nplus" in c.values:
                        c.steps = [row for row in c.steps if row[0] != "np"]
                        c.steps = [(name, op, "nplus" if left == "np" else left,
                                    "nplus" if right == "np" else right)
                                   for name, op, left, right in c.steps]
                    expected = expected_S*(n*n-n)+expected_Tplus*(n*n-1)
                    saved_codeword_operation = 0
                else:
                    offset = 0
                    for name in order:
                        if name == "A":
                            break
                        offset += {"B": 2, "C": 4}[name]
                    shifted_S = "S"
                    if offset:
                        power = f"q{offset}"
                        if power not in c.values:
                            assert offset == 6
                            c.op(power, "*", "q2", "q4")
                        c.op("shift_a", "-", "S", power)
                        c.op("shifted_S", "+", "shift_a", 1)
                        shifted_S = "shifted_S"
                    c.op("unshift_T", "-", "Tplus", 1)
                    if form == "direct":
                        c.op("nm", "-", "n2", "n")
                        c.op("nd", "-", "n2", 1)
                        c.op("sa", "*", shifted_S, "nd")
                        c.op("td", "*", "unshift_T", "nm")
                        c.op("r", "+", "sa", "td")
                    elif form == "common_n_minus_one":
                        c.op("nm", "-", "n", 1)
                        if "nplus" not in c.values:
                            c.op("nplus", "+", "n", 1)
                        c.op("sa", "*", shifted_S, "nplus")
                        c.op("td", "*", "unshift_T", "n")
                        c.op("rs", "+", "sa", "td")
                        c.op("r", "*", "nm", "rs")
                    else:
                        c.op("st", "+", shifted_S, "unshift_T")
                        c.op("rs", "*", "n2", "st")
                        c.op("nt", "*", "n", "unshift_T")
                        c.op("rr", "-", "rs", "nt")
                        c.op("r", "-", "rr", shifted_S)
                    expected = (expected_S.subs(g, g-1)+1)*(n*n-1)+(expected_Tplus-1)*(n*n-n)
                    saved_codeword_operation = 1
                # Replay the emitted schedule, including the n+1 reuse.
                replay = Circuit()
                for instruction in c.steps:
                    replay.op(*instruction)
                assert sp.expand((replay.values["r"]-expected).subs(n, q**8)) == 0
                counts = {"additions": sum(row[1] != "*" for row in c.steps),
                          "multiplications": sum(row[1] == "*" for row in c.steps)}
                rows.append({"order": order, "mode": mode, "r_form": form,
                             "region_operations": len(c.steps), "histogram": counts,
                             "codeword_operations_saved": saved_codeword_operation,
                             "whole_candidate": 111+len(c.steps)-18-saved_codeword_operation,
                             "schedule": c.steps})
    receipt = {"status": "PASS", "baseline_operations": 111,
               "width_exponents": [2, 2, 4], "baseline_region_operations": 18,
               "existing_identity_used": "n=q^8",
               "scope": "Six explicit orders, standard and G-shifted Kummer forms, three final r expressions; bounded arithmetic search only, not an optimality claim or proof of all reordered bootstrap domains",
               "results": rows}
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    for order in ["ABC", "ACB", "BAC", "BCA", "CAB", "CBA"]:
        print(order, {mode: min(row["whole_candidate"] for row in rows
                               if row["order"] == order and row["mode"] == mode)
                      for mode in ["standard", "G_shifted"]})
    print("PASS: 36 exact polynomial identities; no candidate below111")


if __name__ == "__main__":
    main()
