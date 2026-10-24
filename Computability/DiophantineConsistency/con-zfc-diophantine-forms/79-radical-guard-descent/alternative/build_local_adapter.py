#!/usr/bin/env python3
"""Build a literal single-loop LOCAL source adapter from the pinned source.

Usage: python3 build_local_adapter.py [path/to/ProveIt]
The resulting JSON is self-contained, but it is not a final fixed-dimensional
Con(ZFC) polynomial. It still needs beta graphs and bounded-forall closure.
"""
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import json
import sys


PIN = "2605669a532342f153b13eb6b4a0af4b54f5fa37"
RELATIVE = ("Computability/DiophantineConsistency/con-zfc-diophantine-forms/"
            "68-joint-positivity/direct/affine_shared_step.json")
EXPECTED = "c858ecd4f87f06e16d9f7b075ccdfe911af22d928e722a470ca292ec731fdc03"


def require(value, message):
    if not value:
        raise AssertionError(message)


def polynomial(row, values):
    result = 0
    for term in row:
        value = term["coefficient"]
        for name in term["monomial"]:
            value *= values[name]
        result += value
    return result


def evaluate(obj, values):
    product = 1
    for branch in obj["horn_source"]["branches"]:
        product *= polynomial(branch["sum_of_squares"], values)
    return product + sum(polynomial(row, values) ** 2
                         for row in obj["extra_residuals"])


def main():
    here = Path(__file__).resolve().parent
    if len(sys.argv) > 1:
        path = Path(sys.argv[1]) / RELATIVE
    elif (here / "upstream/affine_shared_step.json").is_file():
        path = here / "upstream/affine_shared_step.json"
    else:
        path = here.parent / "ProveIt" / RELATIVE
    raw = path.read_bytes()
    require(sha256(raw).hexdigest() == EXPECTED, "upstream content differs from pin")
    old = json.loads(raw)
    require(old["witness_count"] == 23 and old["exact_degree"] == 50, "old metrics changed")
    new = deepcopy(old)
    new["exposed_coordinates"] = ["S", "Sp", "T", "M0", "i"]
    new["witnesses"] = old["witnesses"][:-3] + ["db", "k"]
    new["witness_count"] = 22
    new["extra_residuals"] = new["extra_residuals"][:1] + [[
        {"coefficient": 1, "monomial": ["p"]},
        {"coefficient": 1, "monomial": ["q"]},
        {"coefficient": 1, "monomial": ["v"]},
        {"coefficient": 1, "monomial": ["db"]},
        {"coefficient": -1, "monomial": ["T"]},
    ]]
    for row in new["extra_residuals"]:
        for term in row:
            term["monomial"] = ["T" if name == "m" else name for name in term["monomial"]]
    new["extra_residuals"].append([
        {"coefficient": 1, "monomial": ["M0"]},
        {"coefficient": 1, "monomial": []},
        {"coefficient": -1, "monomial": ["i", "k"]},
        {"coefficient": -1, "monomial": ["k"]},
    ])
    new["meaning"] = "local affine Horn step plus common-multiple check at the SAME loop index"
    new["status"] = "source arithmetic; final bounded-forall compilation not materialized"
    new["source"] = {"repository": "VladimirReshetnikov/ProveIt", "commit": PIN,
                     "path": RELATIVE, "sha256": EXPECTED}
    new["new_part"] = "three bounds replaced by joint bound p+q+v+db=T; divisor quotient k added"
    degree = sum(max(len(t["monomial"]) for t in b["sum_of_squares"])
                 for b in new["horn_source"]["branches"])
    degree = max(degree, *(2 * max(len(t["monomial"]) for t in row)
                           for row in new["extra_residuals"]))
    require(degree == 50, "degree must remain 50")

    # Exact adapter identities at diverse natural assignments. This tests only
    # the adapter; upstream semantic correctness is an inherited theorem.
    for seed in range(80):
        values = {name: (seed * (j + 3) + j * j) % 7
                  for j, name in enumerate(new["exposed_coordinates"] + new["witnesses"])}
        before = dict(values, m=values["T"], dp=0, dq=0, dv=0)
        residual = values["M0"] + 1 - (values["i"] + 1) * values["k"]
        expected = evaluate(old, before) - sum(polynomial(row, before)**2 for row in old["extra_residuals"][1:])
        expected += (values["p"] + values["q"] + values["v"] + values["db"] - values["T"])**2 + residual**2
        require(evaluate(new, values) == expected,
                "literal adapter identity failed")

    # Truth padding has a local witness for every i<T when M is divisible by
    # i+1. Rule variables and all scratch wires are set to0; slacks equalT.
    truth_checks = 0
    from math import factorial
    for t in range(1,9):
        common = factorial(t)
        for i in range(t):
            values = {name: 0 for name in new["exposed_coordinates"] + new["witnesses"]}
            values.update(S=1, Sp=1, T=t, M0=common - 1, i=i,
                          k=common // (i + 1), db=t)
            require(evaluate(new, values) == 0, "truth-padding local witness failed")
            truth_checks += 1
    (here / "single_loop_local.json").write_text(json.dumps(new, indent=2) + "\n")
    checks = {"status": "pass", "source_sha256": EXPECTED,
              "exact_degree": degree, "local_witnesses": 22,
              "exposed_step_coordinates": 5, "adapter_identity_checks": 80,
              "truth_padding_checks": truth_checks,
              "outer_parameters": 4, "bounded_forall_blocks": 1,
              "final_polynomial_counted": False}
    (here / "LOCAL_ADAPTER_CHECKS.json").write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps(checks, indent=2))


if __name__ == "__main__":
    main()
