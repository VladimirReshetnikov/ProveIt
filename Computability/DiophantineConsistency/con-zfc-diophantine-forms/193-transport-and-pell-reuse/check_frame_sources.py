#!/usr/bin/env python3
"""Replay the optional squared-radix frame and collect both small sources."""
from pathlib import Path
import copy
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "direct_finite_verifier", ROOT / "direct/verify.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def main():
    parent = ROOT / "direct/parent166"
    original = audit.load(parent / "factored_source.json")
    changed = copy.deepcopy(original)
    names = {v["name"]: i for i, v in enumerate(changed["variables"])}
    W, A, q, z, L = [names[n] for n in (
        "shared.W", "shared.A", "pow2.output", "shared.Zminus1", "frame.L")]
    labels = [r["label"] for r in changed["residuals"]]
    frame = labels.index("shared.frame_definition")
    center = labels.index("free_A.cofinal_constructor")
    old = audit.poly(changed["residuals"][frame]["terms"])
    W0 = {m: -c for m, c in old.items() if m != (W,)}
    changed["residuals"][frame]["terms"] = audit.terms(
        audit.plus({(W,): 1}, audit.times({(q, q): -1}, W0)))
    changed["residuals"][center]["terms"] = audit.terms(
        {(A,): 1, (L, L): -1, (z, z): -8, (z,): -8, (): -2})
    out = audit.replay_affine(audit.replay_stage(changed, parent), parent)
    keep = [i for i, v in enumerate(out["variables"])
            if v["name"] not in ("free_A.u", "free_A.v")]
    rows = [audit.poly(r["terms"]) for r in out["residuals"]]
    out = audit.cut(out, rows, list(range(len(rows))), keep)
    wanted = audit.load(ROOT / "direct/frame_alternatives/q2_equation.json")
    audit.demand(out == audit.mathdata(wanted),
                 "Squared-radix frame does not replay from the retained parent")
    results = {}
    for exponent, source in [(1, audit.load(ROOT / "direct/source227.json")),
                             (2, wanted)]:
        residuals = [audit.poly(r["terms"]) for r in source["residuals"]]
        collected = {}
        for residual in residuals:
            collected = audit.plus(collected, audit.times(residual, residual))
        measured = {
            "degree": max(len(m) for m in collected),
            "height": max(abs(c) for c in collected.values()),
            "max_residual_coefficient": max(
                abs(c) for r in residuals for c in r.values()),
            "max_residual_degree": max(len(m) for r in residuals for m in r),
            "monomials": len(collected),
            "residuals": len(residuals),
            "variables": len(source["variables"]),
        }
        advertised = audit.load(
            ROOT / f"direct/frame_alternatives/q{exponent}_METRICS.json")
        audit.demand(measured == advertised, "Collected frame metrics differ")
        results[f"q{exponent}"] = measured
    print(json.dumps({"status": "PASS", "squared_radix_replay": "exact",
                      "collected_sources": results}, indent=2))


if __name__ == "__main__":
    main()
