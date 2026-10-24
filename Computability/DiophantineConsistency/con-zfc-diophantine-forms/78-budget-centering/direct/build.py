#!/usr/bin/env python3
"""Build the literal local polynomial using the bundled pinned Horn rows.

No network, imports from upstream executable code, or unbounded compilation.
The result is a LOCAL source, not a finished consistency polynomial.
"""
import json
from pathlib import Path
from core import pconst, pvar, padd, psub, pmul, psos, pdegree, rows, parse

HERE = Path(__file__).resolve().parent


def build():
    basis = json.loads((HERE / "horn_source_rows.json").read_text())
    s, sp, t, tp, m, p, q, v, u, w = map(
        pvar, ["S", "Sp", "T", "Tp", "M", "p", "q", "v", "q0", "q1"])
    one = pconst(1)
    branches = []
    for original in basis["branches"]:
        name = original["name"]
        source_rows = [parse(r) for r in original["residuals"]]
        if name == "truth":
            arity = 0
            extra = [psub(pmul(sp, m), s), psub(tp, t)]
            new_wires = []
        elif name == "mp":
            arity = 2
            new_wires = [
                {"name": "q0", "value": rows(pmul(s, padd(m, p)))},
                {"name": "q1", "value": rows(pmul(p, q))}]
            extra = [
                psub(u, pmul(s, padd(m, p))),
                psub(pmul(sp, padd(m, v)), pmul(u, padd(m, q))),
                psub(w, pmul(p, q)),
                psub(tp, pmul(t, padd(padd(padd(padd(one, p), q), w), v)))]
        elif name == "gen":
            arity = 1
            new_wires = []
            extra = [
                psub(pmul(sp, padd(m, v)), pmul(s, padd(m, p))),
                psub(tp, pmul(t, padd(padd(one, p), v)))]
        else:
            arity = 0
            new_wires = []
            extra = [
                psub(pmul(sp, padd(m, v)), s),
                psub(tp, pmul(t, padd(one, v)))]
        residuals = source_rows + extra
        sos = psos(residuals)
        wire_names = [w["name"] for w in original["wires"] + new_wires]
        if len(wire_names) != len(set(wire_names)):
            raise ValueError("source and flow wires overlap in one active branch")
        if any(pdegree(r) > 2 for r in extra):
            raise ValueError("new arithmetic row is not quadratic")
        branches.append({
            "name": name, "actual_arity": arity,
            "original_residual_count": len(source_rows),
            "new_residual_count": len(extra),
            "wires": original["wires"] + new_wires,
            "residuals": [rows(r) for r in residuals],
            "sum_of_squares": rows(sos),
            "exact_degree": pdegree(sos),
            "monomial_count": len(sos)})
    witnesses = ["p", "q", "v", "a", "b", "c", "d"] + [f"q{i}" for i in range(13)]
    obj = {
        "title": "Local linear-factor Horn source with a coefficient budget",
        "domain": "nonnegative integers",
        "scope": "local source only; no final bounded-forall compilation or consistency polynomial count",
        "exposed_coordinates": ["S", "Sp", "T", "Tp", "M"],
        "witnesses": witnesses,
        "witness_count": len(witnesses),
        "polynomial": "product, over all branches, of the displayed sum_of_squares polynomials",
        "exact_degree": sum(b["exact_degree"] for b in branches),
        "branches": branches,
        "source_provenance": basis["provenance"],
        "global_interface": {
            "outer_coordinates": ["N", "x", "y", "M"],
            "beta": "beta(x,y,j)=x mod (1+(j+1)*y)",
            "S_i": "beta(x,y,2*i)",
            "T_i": "beta(x,y,2*i+1)",
            "endpoints": ["S_0=M+1", "S_N=1", "T_0=1", "M=T_N+1"],
            "bounded_families": 1}}
    metrics = {
        "status": "local exact arithmetic only",
        "local_witnesses": len(witnesses),
        "exposed_local_coordinates": len(obj["exposed_coordinates"]),
        "local_degree": obj["exact_degree"],
        "branches": len(branches),
        "max_shared_wire_index_plus_one": 13,
        "original_rows": sum(b["original_residual_count"] for b in branches),
        "new_rows": sum(b["new_residual_count"] for b in branches),
        "new_rows_max_degree": 2,
        "branch_degrees": {b["name"]: b["exact_degree"] for b in branches},
        "comparison": {
            "baseline": "source 68/direct/affine_shared_step.json",
            "same_pinned_horn_rows": True,
            "old_local_witnesses": 23, "new_local_witnesses": 20,
            "old_exposed_local_coordinates": 4, "new_exposed_local_coordinates": 5,
            "old_local_degree": 50, "new_local_degree": 52,
            "old_outer_coordinates": 5, "new_outer_coordinates": 4,
            "old_bounded_families": 2, "new_bounded_families": 1,
            "old_beta_outputs_per_step": 2, "new_beta_outputs_per_step": 4,
            "warning": "These are source-interface counts, not final polynomial counts."}}
    (HERE / "linear_budget_local.json").write_text(json.dumps(obj, indent=2) + "\n")
    (HERE / "LOCAL_METRICS.json").write_text(json.dumps(metrics, indent=2) + "\n")
    print(json.dumps(metrics, indent=2))


if __name__ == "__main__":
    build()
