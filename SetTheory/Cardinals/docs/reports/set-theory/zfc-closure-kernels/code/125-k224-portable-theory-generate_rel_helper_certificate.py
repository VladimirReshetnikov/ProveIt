#!/usr/bin/env python3
"""Build actual Rel-code-helper proofs, expanding every symmetry premise.

Uses the unmodified Source116 proof constructors. The independent checker
imports none of these generators. No V_eq or primitive symmetry leaf is kept.
"""
from __future__ import annotations
import argparse
from functools import cache
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "source116" / "proofs"))
import equality_certificates as e
import indiscernibility_certificates as g


def rel_code(a, b):
    return 4 * ((a + b) * (a + b + 1) // 2 + b) + 1


def helper(a, b):
    atom = e.Eq(a, b)
    return e.P("REL_HELPER", e.I(atom, e.Q(rel_code(a, b), atom)))


@cache
def primitive_refl(x):
    z = rel_code(x, x)
    d, atom = e.Eq(z, x), e.Eq(x, x)
    to_atom = e.abst(d, e.mp(e.mp(e.rho7(x, x, z), e.hyp(d)), e.hyp(d)))
    some_atom = e.mp(e.emono(z, to_atom), e.rho1(z, x))
    some_all = e.mp(e.emono(z, helper(x, x)), some_atom)
    return e.mp(e.rho6(z, atom), some_all)


@cache
def primitive_sym(x, y):
    atom = e.Eq(x, y)
    return e.abst(atom, e.mp(e.mp(e.rho7(y, x, x), e.hyp(atom)), primitive_refl(x)))


def eq_to_E(a, b):
    atom = e.Eq(a, b)
    if a == b:
        return e.mp(e.k(g.E(a, b), atom), g.e_refl(a))
    z = rel_code(a, b)
    pieces = []
    for out in (False, True):
        forward = g.left(a, b, z) if out else g.right(a, b, z)
        reverse = g.left(b, a, z) if out else g.right(b, a, z)
        body = g.body(a, b, z, out)
        implication = g.prop(e.I(atom, body), forward, primitive_sym(a, b), reverse)
        pieces.append(g.prop(e.I(atom, e.Q(z, body)), helper(a, b), e.mono(z, implication)))
    initial = g.prop(e.I(atom, g.Ez(a, b, z)), *pieces)
    return g.prop(e.I(atom, g.E(a, b)), initial, g.aux(a, b, z, g.weq(a, b)))


@cache
def expand_symmetry(p):
    if p.rule in ("SYM", "Sym"):
        a, b = p.form[1][1:]
        return expand_symmetry(primitive_sym(a, b))
    if p.rule == "MP":
        return e.mp(*(expand_symmetry(q) for q in p.args))
    if p.rule == "GEN":
        return e.gen(p.args[0], expand_symmetry(p.args[1]))
    if p.rule == "V_eq":
        raise ValueError("unexpected old canonical Eq-code helper")
    return p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "rel_helper_certificate.json")
    a = parser.parse_args()
    roots = {}
    for x in (0, 1, 7, 999):
        roots[f"primitive_refl/{x}"] = primitive_refl(x)
        roots[f"primitive_sym/{x}/0"] = primitive_sym(x, 0)
    for x, y in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 7), (100, 999)):
        bridge = eq_to_E(x, y)
        roots[f"eq_to_E/{x}/{y}"] = bridge
        roots[f"exists_E/{x}/{y}"] = e.mp(e.emono(x, bridge), e.rho1(x, y))
        k = g.weq(x, y)
        roots[f"E_vacuity/{x}/{y}/{k}"] = g.e_vac(x, y, k)
        for z in sorted({0, x, y, k}):
            roots[f"E_in/{x}/{y}/{z}"] = g.e_rel(x, y, z)
            roots[f"E_out/{x}/{y}/{z}"] = g.e_rel(x, y, z, True)
    for x, y, z in ((0, 0, 0), (0, 1, 1), (2, 7, g.weq(2, 7)), (999, 0, 100)):
        roots[f"E_rho7/{x}/{y}/{z}"] = g.e_rho7(x, y, z)
    roots = {name: expand_symmetry(p) for name, p in roots.items()}
    if any(e.assumptions(p) for p in roots.values()):
        raise ValueError("open root")
    data = e.export(roots)
    data["format"] = "actual-rel-helper-bootstrap-v1"
    data["scope"] = "Actual Rel(a,b)-code helper; all primitive symmetry leaves expanded; no V_eq. TAUT abbreviates the retained rho8/rho6 classical propositional calculus. Uniform K coupling is proved separately."
    a.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps({"certificate": str(a.output), "roots": len(roots),
                      "proof_nodes": len(data["proof_nodes"]), "formulas": len(data["formulas"])}, indent=2))


if __name__ == "__main__":
    main()
