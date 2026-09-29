#!/usr/bin/env python3
"""Bounded affine code/packing frontier search after the 107 certificate.

W=q^2(Y+q^2*sigma), A=n^2-n, D=n^2-1 and Tplus are already computed.
The baseline region forms C=x+g, S=g+W, and r=A*S+D*Tplus in five ops.
Some variants supply C or S instead of g. Their counts are arithmetic
frontier counts only: positivity of the reconstructed g is not assumed
free, and no new equivalent Diophantine system is claimed for a variant.
"""
import json
from pathlib import Path
import sympy as sp

x, g, C, S, W, n, T, J = sp.symbols("x g C S W n Tplus J")
A = n*n-n
D = n*n-1


class Circuit:
    def __init__(self):
        self.env = {"x": x, "g": g, "C_input": C, "S_input": S,
                    "W": W, "A": A, "D": D, "n": n, "n2": n*n,
                    "Tplus": T, "J_input": J}
        self.rows = []

    def op(self, name, operation, left, right):
        a = self.env[left] if isinstance(left, str) else sp.Integer(left)
        b = self.env[right] if isinstance(right, str) else sp.Integer(right)
        self.env[name] = {"+": lambda: a+b, "-": lambda: a-b,
                          "*": lambda: a*b}[operation]()
        self.rows.append((name, operation, left, right))

    def direct_r(self, S_name):
        self.op("SA", "*", S_name, "A")
        self.op("TD", "*", "Tplus", "D")
        self.op("r", "+", "SA", "TD")


def main():
    results = []

    def save(name, c, expected, substitution=None, removed_global_ops=0, domain_note=""):
        actual = c.env["r"]
        if substitution:
            actual = actual.subs(substitution)
        assert sp.expand(actual-expected) == 0
        histogram = {"additions": sum(row[1] != "*" for row in c.rows),
                     "multiplications": sum(row[1] == "*" for row in c.rows)}
        results.append({"name": name, "region_operations": len(c.rows),
                        "removed_global_operations": removed_global_ops,
                        "whole_arithmetic_candidate": 107+len(c.rows)-5-removed_global_ops,
                        "histogram": histogram, "schedule": c.rows,
                        "domain_note": domain_note})

    original_r = A*(g+W)+D*T
    changed_r = A*(C+W-x)+D*T

    c = Circuit()
    c.op("C", "+", "x", "g")
    c.op("S", "+", "g", "W")
    c.direct_r("S")
    save("baseline_g_input", c, original_r)

    for form in ["subtract_x_first", "subtract_x_from_W", "sum_first"]:
        c = Circuit()
        if form == "subtract_x_first":
            c.op("g_reconstructed", "-", "C_input", "x")
            c.op("S", "+", "g_reconstructed", "W")
        elif form == "subtract_x_from_W":
            c.op("Wminusx", "-", "W", "x")
            c.op("S", "+", "C_input", "Wminusx")
        else:
            c.op("CplusW", "+", "C_input", "W")
            c.op("S", "-", "CplusW", "x")
        c.direct_r("S")
        save("C_input_"+form, c, changed_r,
             domain_note="Requires C>x to preserve positive g; no cost-free domain assertion is claimed")

    c = Circuit()
    c.op("CplusW", "+", "C_input", "W")
    c.op("positive_term", "*", "A", "CplusW")
    c.op("negative_term", "*", "A", "x")
    c.op("TD", "*", "D", "Tplus")
    c.op("total", "+", "positive_term", "TD")
    c.op("r", "-", "total", "negative_term")
    save("C_input_distribute_input_correction", c, changed_r,
         domain_note="Same reconstructed-g domain issue; splitting x*A adds a multiplication")

    c = Circuit()
    c.op("SminusW", "-", "S_input", "W")
    c.op("C", "+", "SminusW", "x")
    c.direct_r("S_input")
    assert sp.expand(c.env["C"]-(S-W+x)) == 0
    save("S_input_reconstruct_code", c, A*S+D*T,
         domain_note="Requires S>W to preserve positive g; no free domain assertion is claimed")

    c = Circuit()
    c.op("J_rhs", "+", "C_input", "W")
    c.op("S", "-", "J_input", "x")
    c.direct_r("S")
    save("supplied_joint_sum_J", c, changed_r, {J: C+W},
         domain_note="Includes one arithmetic operation for the free equality J=C+W; still requires positive reconstructed g")

    c = Circuit()
    c.op("CplusW", "+", "C_input", "W")
    c.op("S", "-", "CplusW", "x")
    c.op("ST", "+", "S", "Tplus")
    c.op("n2ST", "*", "n2", "ST")
    c.op("nS", "*", "n", "S")
    c.op("remainder", "-", "n2ST", "nS")
    c.op("r", "-", "remainder", "Tplus")
    save("C_input_compute_S_plus_T", c, changed_r, removed_global_ops=2,
         domain_note="A and D are not computed in this variant; reconstructed-g positivity still needs justification")

    c = Circuit()
    c.op("CplusW", "+", "C_input", "W")
    c.op("S", "-", "CplusW", "x")
    c.op("nm1", "-", "n", 1)
    c.op("np1", "+", "n", 1)
    c.op("nS", "*", "n", "S")
    c.op("npT", "*", "np1", "Tplus")
    c.op("inner", "+", "nS", "npT")
    c.op("r", "*", "nm1", "inner")
    save("C_input_factor_n_minus_one", c, changed_r, removed_global_ops=2,
         domain_note="A and D are removed; reconstructed-g positivity still needs justification")

    c = Circuit()
    c.op("C_constraint_rhs", "+", "x", "g")
    c.op("S", "+", "g", "W")
    c.direct_r("S")
    save("extra_positive_C_keep_positive_g", c, original_r,
         domain_note="Fully preserves positivity with the extra free equality C=x+g; no arithmetic saving")

    assert min(row["whole_arithmetic_candidate"] for row in results) == 107
    receipt = {"status": "PASS", "baseline_operations": 107,
               "baseline_measured_operations": 5, "cases": results,
               "frontier": "W=q^2(Y+q^2*sigma), A=n^2-n, D=n^2-1, Tplus already available",
               "scope": "Ten exact affine frontier factorizations; no global circuit-optimality claim and no unproved positive-domain equivalence claimed",
               "observation": "With C supplied, the packed sum C+W-x still requires two affine operations; the missing x correction is not free"}
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    for row in results:
        print(row["name"], row["whole_arithmetic_candidate"])
    print("PASS: ten exact identities; no affine-frontier improvement below107")


if __name__ == "__main__":
    main()
