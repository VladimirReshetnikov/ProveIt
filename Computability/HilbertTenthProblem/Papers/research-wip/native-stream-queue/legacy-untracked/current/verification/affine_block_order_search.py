#!/usr/bin/env python3
"""Bounded exact search of six block orders; does not claim circuit optimality.

The measured region starts after S2,S3,L2,Z*lambda,l*q,q^2,q^4,q^8,n^2
have already been computed by the frozen 112-operation certificate. Each
candidate includes construction of S,T+1 and the final r expression. All
expressions are checked as exact polynomials after the geometric identity.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

q, n, g, e, ell, B, b, lam, zl, s3 = sp.symbols("q n g e ell B b lam zl s3")


class Circuit:
    def __init__(self):
        self.values = {
            "q": q, "n": n, "g": g, "e": e, "l": ell,
            "B": B, "b": b, "la": lam, "zl": zl, "S3": s3,
            "S2": e + ell*q, "L2": lam + q*q, "lq": ell*q,
            "q2": q*q, "q4": q**4, "q8": q**8, "n2": n*n,
        }
        self.steps = []

    def op(self, name, operator, left, right):
        lv = self.values[left] if isinstance(left, str) else sp.Integer(left)
        rv = self.values[right] if isinstance(right, str) else sp.Integer(right)
        self.values[name] = {"+": lambda: lv+rv, "-": lambda: lv-rv,
                             "*": lambda: lv*rv}[operator]()
        self.steps.append((name, operator, left, right))
        return name


def blocks(order):
    c = Circuit()
    c.op("u", "-", "b", 1)
    c.op("v", "-", "B", 2)
    if order == "ABC":
        c.op("s_a", "*", "q2", "S3")
        c.op("s_b", "+", "S2", "s_a")
        c.op("s_c", "*", "q", "s_b")
        c.op("S", "+", "g", "s_c")
        c.op("tc", "-", "L2", "zl")
        c.op("ta", "*", "q", "tc")
        c.op("tb", "*", "l", "u")
        c.op("td", "-", "ta", "tb")
        c.op("te", "*", "lq", "q2")
        c.op("tf", "*", "v", "te")
        c.op("Tplus", "+", "td", "tf")
    elif order == "BAC":
        c.op("s_a", "*", "q", "S3")
        c.op("s_b", "+", "g", "s_a")
        c.op("s_c", "*", "q2", "s_b")
        c.op("S", "+", "S2", "s_c")
        c.op("ta", "*", "v", "q")
        c.op("tb", "-", "ta", "u")
        c.op("tc", "*", "lq", "tb")
        c.op("td", "+", "q2", "tc")
        c.op("te", "*", "q", "td")
        c.op("tf", "-", "la", "zl")
        c.op("Tplus", "+", "te", "tf")
    elif order == "ACB":
        c.op("q6", "*", "q2", "q4")
        c.op("s_a", "*", "q", "S3")
        c.op("s_b", "*", "q6", "S2")
        c.op("s_c", "+", "g", "s_a")
        c.op("S", "+", "s_c", "s_b")
        c.op("ta", "-", "L2", "zl")
        c.op("tb", "-", "ta", 1)
        c.op("tc", "*", "q6", "tb")
        c.op("td", "*", "v", "q")
        c.op("te", "-", "td", "u")
        c.op("tf", "*", "l", "te")
        c.op("tg", "+", "q", "tc")
        c.op("Tplus", "+", "tg", "tf")
    elif order == "BCA":
        c.op("q5", "*", "q", "q4")
        c.op("q7", "*", "q5", "q2")
        c.op("s_a", "*", "q5", "g")
        c.op("s_b", "+", "S3", "s_a")
        c.op("s_c", "*", "q2", "s_b")
        c.op("S", "+", "S2", "s_c")
        c.op("ta", "-", "L2", "zl")
        c.op("tb", "+", "ta", "q8")
        c.op("tc", "-", "tb", "q7")
        c.op("td", "*", "q5", "u")
        c.op("te", "-", "v", "td")
        c.op("tf", "*", "lq", "q")
        c.op("tg", "*", "tf", "te")
        c.op("Tplus", "+", "tc", "tg")
    elif order == "CAB":
        c.op("q5", "*", "q", "q4")
        c.op("q6", "*", "q2", "q4")
        c.op("s_a", "*", "q", "S2")
        c.op("s_b", "+", "g", "s_a")
        c.op("s_c", "*", "q5", "s_b")
        c.op("S", "+", "S3", "s_c")
        c.op("ta", "-", "la", "zl")
        c.op("tb", "*", "q6", "ta")
        c.op("tc", "+", "q8", 1)
        c.op("td", "-", "tc", "q5")
        c.op("te", "*", "q5", "u")
        c.op("tf", "-", "v", "te")
        c.op("tg", "*", "l", "tf")
        c.op("th", "+", "tb", "td")
        c.op("Tplus", "+", "th", "tg")
    elif order == "CBA":
        c.op("q5", "*", "q", "q4")
        c.op("q7", "*", "q5", "q2")
        c.op("s_a", "*", "q2", "g")
        c.op("s_b", "+", "S2", "s_a")
        c.op("s_c", "*", "q5", "s_b")
        c.op("S", "+", "S3", "s_c")
        c.op("ta", "-", "la", "zl")
        c.op("tb", "-", "ta", 1)
        c.op("tc", "*", "q5", "tb")
        c.op("td", "*", "q7", "u")
        c.op("te", "-", "v", "td")
        c.op("tf", "*", "l", "te")
        c.op("tg", "+", "q8", 1)
        c.op("th", "+", "tg", "tc")
        c.op("Tplus", "+", "th", "tf")
    else:
        raise ValueError(order)
    return c


def target(order):
    data = {"A": (g, q-1-(b-1)*ell, 1),
            "B": (e+ell*q, q*q-1+lam-zl, 2),
            "C": (s3, (B-2)*ell, 5)}
    S = T = 0
    width = 0
    for name in order:
        si, ti, wi = data[name]
        S += q**width * si
        T += q**width * ti
        width += wi
    assert width == 8
    return S, T+1


def finish(c, form):
    if form == "direct":
        c.op("nm", "-", "n2", "n")
        c.op("sa", "*", "S", "nm")
        c.op("nd", "-", "n2", 1)
        c.op("td", "*", "Tplus", "nd")
        c.op("r", "+", "sa", "td")
    elif form == "common_n_minus_one":
        c.op("nm", "-", "n", 1)
        c.op("np", "+", "n", 1)
        c.op("sa", "*", "n", "S")
        c.op("tb", "*", "np", "Tplus")
        c.op("rs", "+", "sa", "tb")
        c.op("r", "*", "nm", "rs")
    elif form == "sum_of_blocks":
        c.op("st", "+", "S", "Tplus")
        c.op("rs", "*", "n2", "st")
        c.op("ns", "*", "n", "S")
        c.op("rr", "-", "rs", "ns")
        c.op("r", "-", "rr", "Tplus")
    else:
        raise ValueError(form)


def main():
    rows = []
    for order in ["ABC", "ACB", "BAC", "BCA", "CAB", "CBA"]:
        expected_S, expected_T = target(order)
        for form in ["direct", "common_n_minus_one", "sum_of_blocks"]:
            c = blocks(order)
            assert sp.expand(c.values["S"]-expected_S) == 0
            assert sp.expand(c.values["Tplus"]-expected_T) == 0
            packing_cost = len(c.steps)
            finish(c, form)
            assert sp.expand(c.values["r"]-expected_S*(n*n-n)-expected_T*(n*n-1)) == 0
            histogram = {"additions": sum(row[1] != "*" for row in c.steps),
                         "multiplications": sum(row[1] == "*" for row in c.steps)}
            rows.append({"order": order, "r_form": form,
                         "operations": len(c.steps), "packing_operations": packing_cost,
                         "histogram": histogram, "schedule": c.steps,
                         "whole_certificate_candidate": 112+len(c.steps)-18})
    affine_rows = []
    for order in ["ABC", "ACB", "BAC", "BCA", "CAB", "CBA"]:
        c = blocks(order)
        original_S, original_Tplus = target(order)
        offset = 0
        for name in order:
            if name == "A":
                break
            offset += {"B": 2, "C": 5}[name]
        if offset:
            power = f"q{offset}"
            assert power in c.values
            c.op("shift_S", "-", "S", power)
            c.op("shift_S_plus", "+", "shift_S", 1)
            shifted_S = "shift_S_plus"
        else:
            shifted_S = "S"
        c.op("unshift_T", "-", "Tplus", 1)
        c.op("nm", "-", "n2", "n")
        c.op("nd", "-", "n2", 1)
        c.op("sa", "*", shifted_S, "nd")
        c.op("td", "*", "unshift_T", "nm")
        c.op("r", "+", "sa", "td")
        expected_S = original_S.subs(g, g-1)+1
        expected_T = original_Tplus-1
        assert sp.expand(c.values[shifted_S]-expected_S) == 0
        assert sp.expand(c.values["unshift_T"]-expected_T) == 0
        assert sp.expand(c.values["r"]-expected_S*(n*n-1)-expected_T*(n*n-n)) == 0
        affine_rows.append({
            "order": order, "operations": len(c.steps),
            "codeword_operations_saved": 1,
            "whole_certificate_candidate": 112+len(c.steps)-18-1,
            "schedule": c.steps,
            "interpretation": "g here denotes positive G; decoded digit code is G-1",
        })
    receipt = {"status": "PASS", "baseline_operations": 112,
               "baseline_measured_region_operations": 18,
               "scope": "Six explicit factorizations times three r forms; no optimality claim",
               "results": rows, "affine_symmetric_kummer": affine_rows}
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    for row in rows:
        if row["r_form"] == "direct":
            print(row["order"], row["operations"], row["histogram"],
                  "whole candidate", row["whole_certificate_candidate"])
    for row in affine_rows:
        print("affine", row["order"], "whole candidate", row["whole_certificate_candidate"])
    print("PASS: all 18 original and 6 affine polynomial identities")


if __name__ == "__main__":
    main()
