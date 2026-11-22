# Helly's theorem in intuitionistic primitive recursive arithmetic

Read **helly.pdf** for the proof. Its editable source is **helly.tex**. The main construction takes a table of local rational points and computes one common point. A separate barycentric certificate for each set expresses that point using only local witnesses belonging to the set.

## Contents

| Path | Result |
| --- | --- |
| helly.pdf, helly.tex | Uniform iPRA proof, exact polyhedral alternative, centerpoint application, real approximation theorem, exact-selection obstruction, weak exact formulation and the object-theory Lean roadmap |
| lean/Helly.lean | Complete kernel-checked finite rational Helly theorem and constructive rational Radon lemma |
| lean/Precision.lean | Two-sided error bounds for barycentric rows after clearing denominators, including regularity and snapshot estimates |
| lean/SelectionBoundary.lean | Finite-prefix interval witnesses, parity exclusion and the diagonal contradiction from an index for the selector |
| code/helly.py | Exact certificate generator, independent verifier and optional reduction to at most d+1 positive entries per row |
| code/polyhedra.py | Exact rational feasibility by Fourier–Motzkin elimination and a Helly alternative for grouped inequalities |
| code/test_*.py | Reproducible exact-arithmetic tests |

The Lean theorem is a host-language formalization. The paper gives the proof and compilation plan for the separate first-order judgment in ProveIt's embedded iPRA. The real-coordinate result distinguishes an approximation at each precision, a double-negated existence statement at fixed sizes, and a uniform exact operation.

## Reproduce

Run the following commands from the extracted directory, with Python 3.9 or later, Lean 4.19.0, and a standard LaTeX installation as needed.

    (cd code && python3 -B -m unittest discover -v)
    (cd lean && lean Helly.lean && lean Precision.lean && lean SelectionBoundary.lean)
    pdflatex -halt-on-error helly.tex
    pdflatex -halt-on-error helly.tex

The Lean files use only the standard library. The axiom audit for the main result is described in lean/README.md. The source references ProveIt revision 022dfb4c54c22782f927a903f25bcf6491b7eba2.

## Try the square from the proof

Run Python from the code directory. Keys are the increasing tuples of set labels in each local subfamily. The point indexed by a triple is known to lie in its three sets.

    from helly import helly, verify

    local = {
        (1, 2, 3): (0, 0),
        (0, 2, 3): (2, 0),
        (0, 1, 3): (2, 2),
        (0, 1, 2): (0, 2),
    }
    cert = helly(2, 4, local, compact=True)
    assert cert.point == (1, 1)
    assert verify(2, 4, local, cert)
    print(cert.rows)

All coordinates and weights are integers or fractions.Fraction values. The verifier checks membership in the convex hull of incident local points for each index. Membership of input points in the original sets is the caller's hypothesis. For rational halfspace descriptions, decide_family in code/polyhedra.py performs the local feasibility checks itself.
