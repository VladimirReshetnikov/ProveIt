#!/usr/bin/env python3
"""Exact, scoped evidence for deleting the binary radix-threshold equation.

This is an obstruction experiment, not a valid 89-operation universal
certificate. Its companion note proves the full positive extension.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sympy as sp

import round37_1980_binary_product_certificate as published


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def symbolic_deletion():
    schedule = [row for row in published.SCHEDULE if row[0] != "theta_sum"]
    need(len(schedule) == len(published.SCHEDULE)-1, "exactly one instruction removed")
    removed = [row for row in published.SCHEDULE if row[0] == "theta_sum"]
    need(removed == [("theta_sum", "+", "H", "b")], "exact deleted instruction")
    need(published.EQUALITIES[3] == ("th", "theta_sum"), "exact deleted equality")
    equalities = [(i, pair) for i, pair in enumerate(published.EQUALITIES) if i != 3]
    consumers = {operand for _, _, lhs, rhs in schedule for operand in (lhs, rhs)
                 if isinstance(operand, str)}
    need("theta_sum" not in consumers and "H" not in consumers,
         "neither the removed register nor the threshold remains in arithmetic")
    histogram = Counter(row[1] for row in schedule)
    need(len(schedule) == 89 and histogram["*"] == 48
         and histogram["+"]+histogram["-"] == 41,
         "the rejected candidate has 89 instructions")

    env = dict(published.SYM)
    published.baseline.run_schedule(schedule, env)
    s = published.SYM
    source = [sp.expand(row.subs(s["H"], s["th"]-s["b"]))
              for row in published.source_residuals()]
    need(source[3] == 0, "the deleted relation is zero in the fresh theta-based source")
    u = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {16: source[15]*(u*u-s["y_aux"]**2)}
    records = []
    for index, (left, right) in equalities:
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index, sp.Integer(0))
        if sp.expand(actual-source[index]-correction) == 0:
            sign = 1
        elif correction == 0 and sp.expand(actual+source[index]) == 0:
            sign = -1
        else:
            raise AssertionError("fresh source mismatch at "+str(index))
        need(s["H"] not in source[index].free_symbols, "fixed H has disappeared")
        records.append({
            "published_source_index": index,
            "equality": [left, right],
            "source_sign": sign,
            "source_residual": sp.sstr(source[index]),
            "triangular_correction": sp.sstr(sp.expand(correction)),
        })
    need(len(records) == 21, "all remaining equalities checked")
    return {
        "instructions": len(schedule), "multiplications": 48, "additions": 41,
        "positive_unknowns": 34, "equalities": len(records),
        "deleted_instruction": removed[0], "deleted_equality": published.EQUALITIES[3],
        "source_residual_checks": records,
    }


def exact_case(L, V):
    B, theta, b, x, beta, g, ell, C = 4, 2, 3, 2, 1, 4, 4, 6
    e, q = 4**(L-4), 4**L
    n = q**8
    lam = (q*q-1)//3
    sigma, alpha = 36*(e-4), 220*e+140
    need(L >= 6 and 0 < V < q and V % 2 == 0, "tested parameter range")
    need(b == x+beta and C == x+g, "positive input and code identities")
    need(theta+2 == B and theta == b-1, "both tested small-radix descriptions")
    need(q*q == 1+lam*(theta+1), "unchanged certificate geometry")
    need(sigma == (e-ell)*C*C, "positive code product")
    need(ell+sigma+alpha == q, "the original strong product bound is retained")
    need(all(value > 0 for value in (b,beta,g,ell,e,sigma,alpha,lam)),
         "all supplied coding witnesses are positive")
    need(ell < q and e < q and C*C < q and sigma < q, "all original code bounds")
    S2 = ell+e*q
    t = (S2-V)//theta
    need(t > 0 and S2 == V+t*theta, "exact positive fixed-index quotient")
    S = g+q*q*(S2+q*q*sigma)
    Tplus = q*q*(1+theta*lam)+ell*(theta*q**4-b)
    T1, T2, T3 = q*q-13, 2*lam, 8
    need(Tplus-1 == T1+q*q*T2+q**4*T3, "exact three-block mask")
    need(0 < S2 < q*q and 0 < T1 < q*q and 0 < T2 < q*q and 0 < T3 < q**4,
         "all block widths hold")
    need(g & T1 == 0 and S2 & T2 == 0 and sigma & T3 == 0,
         "all three complete integer masks pass")
    need(sigma % 16 == 0 and S & (Tplus-1) == 0, "full combined mask passes")
    need(0 < S < q**5+q**4+q*q < n and 0 < Tplus < 9*q**4 < n,
         "strict bounded packing ranges")
    r = S*(n*n-n)+Tplus*(n*n-1)
    need(n*n-1 <= r < 2*n**3 and r % 2 == 0, "bounded even packed index")
    # Legendre's formula identifies the valuation with popcount(r).
    required_valuation = 2*(n.bit_length()-1)
    need(r.bit_count() >= required_valuation,
         "exact central-binomial divisibility checked via its valuation identity")
    need(L < 2*r+1 and B**(3*L) == q**3 < n,
         "explicit necessity bounds replace the false 3L<=B")
    return {
        "L": L, "L_is_power_of_two": L & (L-1) == 0,
        "V_test": "2" if V == 2 else "q/2" if V == q//2 else "q-2",
        "x": x, "B": B, "theta": theta, "b": b, "g": g, "ell": ell,
        "e_bits": e.bit_length(), "sigma_bits": sigma.bit_length(),
        "q_bits": q.bit_length(), "n_bits": n.bit_length(),
        "r_bits": r.bit_length(), "r_popcount": r.bit_count(),
        "required_central_binomial_valuation": required_valuation,
        "positive_congruence_quotient_bits": t.bit_length(),
        "mask_intersections": [g & T1, S2 & T2, sigma & T3],
        "combined_mask_intersection": S & (Tplus-1),
        "old_threshold_bound_3L_le_B": 3*L <= B,
    }


def verify():
    symbolic = symbolic_deletion()
    cases = []
    for L in (6,7,8,16,32,64,128):
        q = 4**L
        for V in (2,q//2,q-2):
            cases.append(exact_case(L,V))
    return {
        "status": "PASS",
        "interpretation": "Counterexample evidence; the 89-instruction deletion is unsound.",
        "symbolic_deleted_candidate": symbolic,
        "finite_cases": cases,
        "scope": (
            "All 21 symbolic certificate residuals are checked after deleting the single "
            "threshold instruction/equality. The 21 finite cases check coding witnesses, "
            "complete masks, exact packed r and its central-binomial valuation. The V values "
            "are samples of the proved parity/range, not asserted complete compiler indices. "
            "Non-power-of-two L cases are extra arithmetic examples. Enormous complete Pell "
            "witnesses are not instantiated; their existence for every admissible index "
            "is proved in EXPLORATION_BINARY_RADIX_THRESHOLD.md."
        ),
    }


if __name__ == "__main__":
    receipt = verify()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    print(receipt["status"], "21 symbolic residuals;",
          len(receipt["finite_cases"]), "complete-mask cases")
