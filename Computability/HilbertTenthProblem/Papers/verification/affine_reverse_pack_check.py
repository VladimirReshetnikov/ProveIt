#!/usr/bin/env python3
"""Independent arithmetic audit of the reversed-packing 111 proposal.

This is an audit experiment, not a replacement for the frozen certificates.
Positive-domain correctness additionally requires the borrow/bootstrap and
high-mask canonical-remainder argument; polynomial checks do not prove it.
"""
import json
from pathlib import Path
import sympy as sp
import round6_1980_certificate as prior
import round4_1980_operation_count as base
from round4_1980_optimized_certificate import primitive_instructions


def main():
    substitutions = {
        "lq2": ("lq2", "*", "e", "q"),
        "S2": ("S2", "+", "l", "lq2"),
        "bound_sum": ("bound_sum", "+", "S2", "C2"),
        "q4p1": ("q4p1", "+", "q", 1),
        "Sq3": ("Sq3", "*", "Sin", "q2"),
        "Tq3": ("Tq3", "*", "Tcoef", "q2"),
        "packed_target_shift": ("packed_target_shift", "*", "l", "q4"),
    }
    schedule = [substitutions.get(row[0], row) for row in prior.SCHEDULE
                if row[0] != "lC4"]
    sigma = sp.Symbol("sigma")
    s = dict(prior.SYM, sigma=sigma)
    env = dict(s)
    hist = base.run_schedule(schedule, env)
    B = s["H"]*s["b"]**2
    C = 1+s["x"]*B+s["g"]
    Y = s["l"]+s["e"]*s["q"]
    S3 = (2*s["e"]-s["Z"]*s["la"])*C**2+B*s["la"]*(1+s["q"])
    S = s["g"]+s["q"]**2*(Y+s["q"]**2*S3)
    Tplus = s["q"]**2-(s["b"]-1)*s["l"]+s["th"]*s["la"]*s["q"]**2+(B-2)*s["l"]*s["q"]**4
    residuals = list(prior.source_residuals())
    residuals[0] = Y+C**2+s["al"]-s["q"]**2
    residuals[4] = Y-s["V"]-s["t"]*s["th"]
    residuals[6] = s["r"]-S*(s["n"]**2-s["n"])-Tplus*(s["n"]**2-1)
    residuals.append(sigma-S3)
    equalities = list(prior.EQUALITIES)
    equalities[0] = ("L1", "q2")
    equalities.append(("sigma", "S3"))
    Gsrc = 1+(s["a"]+1)*(s["f"]**2-1)
    Gcalc = 1+(s["a"]+1)*env["AE"]
    H17 = 2*s["r"]+1+s["j"]*s["c"]
    corrections = {
        6: (s["la"]*residuals[3]-residuals[2])*s["q"]**2*(s["n"]**2-1),
        16: residuals[15]*(s["a"]+1)*(Gsrc+Gcalc)*H17**2,
    }
    checked = []
    for i, ((left, right), src) in enumerate(zip(equalities, residuals)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(i, 0)
        sign = 1 if sp.expand(actual-src-correction) == 0 else -1
        assert sign == 1 or (correction == 0 and sp.expand(actual+src) == 0), i
        checked.append({"index": i, "equality": [left, right], "sign": sign})
    primitives = primitive_instructions(schedule)
    for row in primitives:
        value = lambda a: sp.Integer(a) if isinstance(a, int) else env[a]
        left, right, result = (value(row[k]) for k in ["left", "right", "result"])
        expected = left+right if row["operation"] == "+" else left*right
        assert sp.expand(expected-result) == 0
    assert len(schedule) == len(primitives) == 111
    assert len(equalities) == 21
    assert sum(row[1] == "*" for row in schedule) == 61
    result = {"status": "PASS", "operations": 111,
              "histogram": hist, "positive_unknowns": 33, "equations": 21,
              "checked_equalities": checked, "schedule": schedule,
              "scope": "Arithmetic only; requires independently audited positive-domain proof"}
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print("PASS: 111 operations, 61 multiplications, 50 additions; 21 equations")


if __name__ == "__main__":
    main()
