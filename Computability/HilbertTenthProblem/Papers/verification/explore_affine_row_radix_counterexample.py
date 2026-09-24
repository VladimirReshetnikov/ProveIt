"""Refute W=8v while verifying its exact 79-operation arithmetic schedule."""

import json
from pathlib import Path
import sympy as sp

import round44_1980_two_auxiliary_history as old


def verify():
    need = old.baseline.need
    outer = [row for row in old.OUTER if row[0] != "v2"]
    outer = [("W", "*", 8, "v") if row[0] == "W" else row for row in outer]
    schedule = outer+old.CORE
    source = old.source_residuals()
    z = old.SYM
    for index in (1, 6):
        source[index] = source[index].subs(z["v"]**3, 8*z["v"])
    env = dict(z)
    old.baseline.run_schedule(schedule, env)
    aux_u = 2*z["r"]+1+z["j"]*z["c"]
    correction = source[16]*(aux_u**2-z["y_aux"]**2)
    records = []
    for index, ((left, right), residual) in enumerate(zip(old.EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        adjustment = correction if index == 17 else sp.Integer(0)
        if sp.expand(actual-residual-adjustment) == 0:
            sign = 1
        elif adjustment == 0 and sp.expand(actual+residual) == 0:
            sign = -1
        else:
            raise AssertionError(f"source mismatch at {index}")
        records.append(dict(index=index, equality=[left, right], source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),
                            correction=sp.sstr(sp.expand(adjustment))))
    primitives, counts = old.verify_primitives(schedule, env)
    need(len(primitives) == 79 and counts == {"+": 34, "*": 45}, "79 primitives")
    need(len(records) == 19, "all 19 equations checked")
    need(sp.expand(env["W"]-8*z["v"]) == 0, "modified row scale")
    need(all(residual.free_symbols <= set(z.values()) for residual in source),
         "declared symbols only")

    q = 16384
    numeric = {"q": q, "v": 2048, "quot": 8, "hrow": 1,
               "Cw": 64, "I": 64, "Bw": 512, "Yw": 256, "F": 256,
               "Uw": 4104, "Vw": 144, "alpha": 7680, "alphaI": 1984}
    T = numeric["Bw"]+numeric["hrow"]
    P = numeric["Uw"]+q*numeric["Vw"]+q*q*numeric["Yw"]+q**3*T
    L, scale, n0 = q**6, q**10, q**5
    lam = (L-1)//7
    need(7*lam == L-1, "positive geometric mask")
    r = (L-P)*(L-1)+6*lam
    numeric.update(lam=lam, r=r)
    substitution = {z[name]: value for name, value in numeric.items()}
    for residual in source[:9]:
        need(residual.subs(substitution) == 0, "exact positive outer equation")
    need(all(value > 0 for value in numeric.values()), "outer positivity")
    need(15*numeric["Bw"]+4*numeric["Yw"] == 8704, "local left value")
    need(numeric["Cw"]+2*numeric["Uw"]+3*numeric["Vw"] == 8704,
         "local right value")
    need(all(0 < field < q for field in [numeric["Uw"], numeric["Vw"],
                                       numeric["Yw"], T]), "all fields fit")
    support = [i for i in range(P.bit_length()) if P >> i & 1]
    need(support == [3, 12, 18, 21, 36, 42, 51], "exact packed support")
    need(all(i % 3 == 0 for i in support), "packed radix-eight Booleanity")
    need(0 < P < q**4 < L, "packed bound")
    need(r % 2 == 0, "even r for positive half-parameter witnesses")
    need(n0 >= 64 and n0 < r < q**12 < n0**3, "Pell growth hypotheses")
    need(scale == n0*n0 == 1 << 140, "exact square scale")
    need(r.bit_count() == 140, "exact central-binomial two-adic valuation")
    need(scale*scale > 2*r+1, "first index and main parameter lower margins")
    need(8*r < scale*(scale+1), "initial ratio error margin")
    need(numeric["F"] == 4*8**2, "invalid positive output digit")

    return dict(
        status="ARITHMETIC_PASS_BUT_ENDPOINT_RELATION_REFUTED",
        arithmetic_status="PASS", endpoint_status="REFUTED",
        operations=79, primitive_histogram=counts,
        unknown_count=len(old.OUTER_NAMES+old.CORE_NAMES), equations=19,
        source_changes=[1, 6], primitive_instructions=primitives,
        equalities=old.EQUALITIES, residuals=records,
        positive_outer_witness={name: str(value) for name, value in numeric.items()},
        packed_word=str(P), packed_binary_support=support,
        r_popcount=r.bit_count(), scale=str(scale), n0=str(n0),
        forbidden_output="F=256=4*8^2",
        scope="All 79 primitive/source identities and the finite outer obstruction "
              "are checked exactly. Existence of the remaining positive Pell "
              "witnesses follows from the established general construction; "
              "they are not numerically materialized.",
        proof_note="../1980/EXPLORATION_AFFINE_ROW_RADIX_COUNTEREXAMPLE.md")


if __name__ == "__main__":
    result = verify()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print("PASS arithmetic79; endpoint relation REFUTED by I64,F256")
    print("All19 source residuals; exact positive outer tuple; evenr; popcount140")
