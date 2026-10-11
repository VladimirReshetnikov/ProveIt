# Integration map

Suggested new report directory:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/ordered-hurwitz-germs/`

Copy this package there as a new report; do not overwrite the existing
`resonant-jets-and-shifts` report. The canonical manuscript can reference
it from the ordered Hurwitz/Stieltjes material and cross-reference the
Mellin hierarchy from the polylogarithm material.

## Source-question disposition

The source is `resonant-jets-and-shifts/sections/08-audit-research.tex`,
Git blob `b9c41fd8cec7205f60cc05c9f71e3873195659de`.

| Source target | Result and labels | Remaining scope |
|---|---|---|
| Question 1: ordered depth three | All-depth polar germ `thm:germ`; ordered coefficients `thm:coefficients`; every transverse triple ray `thm:tripleFP` | Arithmetic reduction of the orientation coordinate is not claimed. |
| Question 2: compatible subtraction | Harmonic cutoff theorem `thm:cutoff`; positive-index logarithmic stuffle character `thm:stuffle`; explicit directional counterterm `cor:counterterm` | Not uniqueness among all prescriptions and not a complete comparison with every existing renormalization scheme. |
| Question 3: nonlinear/tangential paths | Finite-jet algorithm `thm:curve`, every finite-order off-divisor tangency; exact examples `eq:reparam`, `eq:tangent` | Curves contained identically in a polar divisor need a separate restriction operation. |
| Question 6: nonsymmetric Stieltjes sums | Convergent coordinate `prop:omega`; ordinary integral `eq:omegaMellin`; elementary a=1 representation `eq:omegaelementary` | Reduction to a smaller fixed algebra remains open. |

## Entry-point excerpt

`manuscript_fragment.tex` uses the prefix `ohg:` on every label and `OHG`
on helper macros. It can be included in a manuscript with amsmath,
amssymb, amsthm and theorem/proof environments. It is an entry-point
excerpt, not a replacement for the full analytic proofs in article.tex.
For complete canonical integration, carry over the proofs and hypotheses
from the indicated report sections instead of citing successful numerical
replay as their proof.

A smoke test is supplied:

```sh
cd integration
pdflatex -interaction=nonstopmode -halt-on-error smoke_test.tex
```

The fragment's full-half-plane shifted master has a short direct proof;
the report also supplies the independent all-depth coefficient proof.

## Editorial ledger wording

“Constructs a harmonic-compatible ordered common-shift Hurwitz germ at
every finite depth, gives its exact mixed-coefficient recursion and
harmonic-cutoff interpretation, computes all transverse depth-three
constants and all off-divisor curve finite parts, and proves elementary
and Hurwitz-shifted all-depth Mellin generating identities on Re(z)>-1.
The nonsymmetric coordinate is represented by convergent sums and
integrals, not proved arithmetically irreducible or reducible. Classical
continuation/regularization attribution and S6/S8 conjectural status are
preserved.”

The incoming directory metadata was inspected, but the ZIP contents were
not exhaustively reviewed. Deduplication against those packages is still
an integration step. Nothing has been committed or pushed remotely.
