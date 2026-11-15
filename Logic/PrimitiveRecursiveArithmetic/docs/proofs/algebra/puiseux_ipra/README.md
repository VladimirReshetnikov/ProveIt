# Puiseux expansions in intuitionistic primitive recursive arithmetic

## Read this first

The main report is **puiseux_ipra.pdf**. Its complete LaTeX source is
**puiseux_ipra.tex**, with three included section files.

The proved numerical-input theorem takes **finite exact algebraic
presentations** of the polynomial coefficients and expansion point. It
constructs every branch, preserves multiplicities, handles finite poles,
and gives explicit rational convergence radii and tail bounds.

This qualification is substantive. Section 1 proves that a uniform
constructor for exact Puiseux coefficients from arbitrary primitive
recursive Cauchy coefficient names would decide halting, already for a
monic quadratic. The distinction concerns the input presentation, even
when every named value happens to be rational.

## Mathematical result

For degree d, a safe common ramification is N = (d!)^d. A finite
Newton–Hensel calculation, bounded by the discriminant valuation, produces
polynomial simple-root equations. All later coefficients come from fixed
primitive recurrences. Finite weighted coefficient estimates establish
convergence and quantitative tails.

The exact algebraic backend is proved in the appendix. Its one
root-existence dependency is the human-readable one-root constructive FTA
proof already in ProveIt, included unchanged under dependencies/FTA_iPRA.
The present construction supplies the separate uniform exact splitting
argument; it does not assume that repeated numerical deflation is already
uniformly primitive recursive.

## Files

- puiseux_ipra.pdf — compiled main report.
- puiseux_ipra.tex — main LaTeX source.
- convergence.tex — finite majorant proof, factorization, poles, and root selection.
- algebraic_backend.tex — exact algebraic arithmetic and splitting.
- lean_plan.tex — formalization contracts and status.
- lean/PuiseuxTarget.lean — explicit deeply embedded theorem interface.
- lean/LEAN_PLAN.md — detailed implementation order and completion gates.
- code/check_examples.py — exact Gaussian-rational finite-jet checker.
- evidence/example_checks.json — recorded exact checks through order 96.
- evidence/ — mathematical review notes and validation status.
- dependencies/FTA_iPRA/ — unchanged frozen dependency, including its TeX and PDF.
- SOURCE_MANIFEST.md — pinned sources and dependency provenance.
- SHA256SUMS — file-integrity manifest.

## Reproduce the PDF and example checks

With a normal TeX Live installation and Python 3.10 or later:

    latexmk -pdf -interaction=nonstopmode -halt-on-error puiseux_ipra.tex
    python3 code/check_examples.py --cutoff 96 --output evidence/example_checks.json

The Python checker uses only the standard library. It checks five examples:
a cusp, genuine ramification four, repeated factors, Laurent poles, and a
high-contact degree-two polynomial. It checks complete products with their
multiplicities and, where applicable, implicit recurrences and weighted
majorants. These examples are executable evidence, not a proof of the
universal theorem or a general Newton–Puiseux implementation.

## Lean status

**The Lean files are uncompiled outlines.** No Lean or Lake executable was
available in the execution environment. The source targets the inspected
ProveIt snapshot d851229c33ef395db8dc04baf28c6a291073f61e, whose toolchain
is Lean 4.32.0.

The required endpoint is an actual derivation:

    Prf PRAAx [] (PuiseuxSentence concretePrograms)

The included program interface and conditional interpretation theorem do
not construct that derivation. Concrete PR syntax, backend proofs,
the deep FTA derivation, and the Newton/majorant object derivations remain
substantial formalization work. The report gives explicit module contracts
and finite precision bounds for that work. The frozen dependency also
contains an uncompiled Lean specification; it is not a machine-checked
theorem being imported.

## Scope of the mathematical completion

The main report gives a complete human-readable argument for the stated
exact-input theorem, with its explicitly identified FTA dependency included
in full. It also proves the obstruction to the unrestricted uniform
Cauchy-input formulation. It does not claim to have proved that stronger
formulation, nor to have completed the Lean formalization.
