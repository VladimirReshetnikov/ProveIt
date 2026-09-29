#!/usr/bin/env python3
"""Exact finite global packing checks for the rejected packed-bound alias.

Toy supports instantiate the arithmetic identities, bit-clear coordinates,
all three masks and the binary valuation. They are not full universal
layouts or explicit gigantic auxiliary Pell witnesses.
"""
from pathlib import Path
import json

from round32_1980_affine_radix_encoding import need, split_bit_clear


def verify():
    cases = []
    for B in (256, 512, 1024, 2048):
        for K, L in ((8, 32), (10, 64)):
            for x in (1, 2, 17, 65):
                H0, b = 64, B-65
                need(0 < x < b, "positive input gap")
                digits = split_bit_clear(B-1-x, H0)
                g = sum(value*B**(index+1) for index, value in enumerate(digits))
                C = x+g
                q, theta = B**L, B-4
                n = q**8
                la = (q*q-1)//(B-1)
                e = (B**K-1)//(B-1)
                m = B**(K-4)-B*B+B
                ell0 = B+B*B+B**3+B**(K-2)+B**(K-1)
                ell = ell0+m*q
                e0 = e+m
                S2 = ell+e*q
                need(S2 == ell0+e0*q < q*q, "canonical packed coordinate and positive proposed gap")
                need(C % (B-1) == 0, "the physical sum forces exact divisibility")
                A = C*C//(B-1)
                sigma = (la-e)*(q-C*C)
                need(sigma > 0 and sigma % (B**K) == 0, "positive third block has no low target digits")
                need(0 < A+e*C*C < q, "exact remainder bound")
                need(sigma//q == la-e-A*q, "exact high quotient")
                need((sigma//q) % q == (q-1)//(B-1)-e, "high plateau has K initial zero digits")
                need(theta*m < B**K and ((sigma//q) & (theta*m)) == 0, "high alias mask passes")
                first = q*q-1-b*ell
                need(0 <= first < q*q and g & first == 0, "first mask passes")
                need(S2 & (theta*la) == 0, "unchanged middle mask passes")
                need(sigma & (theta*ell) == 0, "complete third mask passes")
                S = g+q*q*S2+q**4*sigma
                Tplus = q*q*(1+theta*la)-b*ell+theta*ell*q**4
                need(0 < S < q**7 < n and 0 < Tplus < q**7 < n, "bounded packing")
                need(S & (Tplus-1) == 0, "global binary no-carry")
                r = S*(n*n-n)+Tplus*(n*n-1)
                need(n*n-1 <= r < 2*n**3, "retained Pell packing bounds")
                needed = 2*(n.bit_length()-1)
                need(r.bit_count() == needed, "central binomial two-adic valuation equals the required exponent")
                cases.append({"B": B, "K": K, "L": L, "x": x,
                              "physical_digits": digits,
                              "valuation_v2_central_binomial": needed,
                              "r_bit_length": r.bit_length()})
    return {"status": "PASS", "scope": "finite exact alias, all three masks, bounded global packing and binary valuation; toy supports, not full auxiliary Pell assignments",
            "proof_note": "../1980/EXPLORATION_AFFINE_PACKED_BOUND_COLLAPSE.md", "cases": cases}


if __name__ == "__main__":
    receipt = verify()
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(receipt["status"], len(receipt["cases"]), "exact global packing and valuation cases")
