# Cover-exacting cardinals and completely definable grounds

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Large_Cardinals_Continuation.tex`: self-contained LaTeX source.
- `Large_Cardinals_Continuation.pdf`: compiled 18-page report.

## Mathematical results

Theorem 5.1 proves a completeness barrier: a short cofinal subset of a gamma-cover-exacting cardinal lambda cannot be gamma-plus-completely definable. Corollary 5.3 extends this exclusion to nontrivial elementary self-embeddings of V_lambda.

Theorem 6.1 proves a strict separation of the power-set sections of HCD(kappa) and HCD(gamma-plus) when kappa < lambda is strongly compact. Corollary 6.3 identifies a precise single-rank stabilization assumption that is inconsistent with this configuration.

Theorem 7.1 and Corollary 7.2 show that a strongly compact delta > gamma makes HCD(delta) a proper forcing ground in which lambda is strongly inaccessible. Thus these hypotheses contradict the Ground Axiom. Section 8 gives explicit approximation/cover failures and a forcing chain-condition obstruction.

Theorem 9.4 proves an equiconsistency refinement of the established ultraexacting/I0 equivalence: lambda may be the first ordinal where HOD and V disagree on cofinality, while their cumulative hierarchies agree through V_lambda.

The proofs use the primary-source results identified in the report. The cover-exacting stationary characterization is from July 2026 research notes. The derived formulations are not independently priority-certified or machine-checked. No unconditional inconsistency of bare cover exactingness, or of its coexistence with a smaller strongly compact cardinal, is claimed.

## Build

Run from this directory:

    pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex
    pdflatex -interaction=nonstopmode -halt-on-error Large_Cardinals_Continuation.tex

A third pass may be useful after substantial edits to pagination. No external bibliography processor or external image assets are needed. The document uses standard TeX packages, including newpxtext, newpxmath, tcolorbox, titlesec, and hyperref.

The typography, page geometry, and Forest/Olive/Muted/Sage/Pale palette follow the supplied unified report. The final build was checked for unresolved references, missing characters, and overfull boxes; the rendered pages were visually inspected.
