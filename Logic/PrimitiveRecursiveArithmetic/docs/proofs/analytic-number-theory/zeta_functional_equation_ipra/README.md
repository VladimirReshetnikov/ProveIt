# Riemann's functional equation in intuitionistic PRA

This package contains a quantitative, human-readable proof of Riemann's
zeta functional equation and a concrete plan for formalizing its finite
arithmetic content in ProveIt's deeply embedded intuitionistic primitive
recursive arithmetic (iPRA).

The main report is the 26-page **`zeta_functional_equation_ipra.pdf`**;
its complete LaTeX source is **`zeta_functional_equation_ipra.tex`**.

## Mathematical content

The proof constructs the theta transformation by finite Fourier and
Fejer estimates, constructs reciprocal gamma from finite Euler products,
proves reflection and duplication without cancelling possibly zero
factors, and identifies the regularized theta Mellin integral with the
zeta Dirichlet series on its convergence half-plane.

Writing `R=1/Gamma`, `X=xi`, and
`Z(s)=pi^(s/2) R(1+s/2) X(s)`, its everywhere-defined target is

```
s R(1-s) Z(s) = (1-s) 2^s pi^(s-1) sin(pi*s/2) Z(1-s).
```

This gives the usual sine-gamma functional equation as a meromorphic
identity. Numerical division requires the stated apartness witnesses.
The report also proves `zeta(0)=-1/2` and residue 1 at the sole zeta pole,
`s=1`.

The internal iPRA statement is a universal correctness sentence for one
fixed primitive-recursive finite residual checker on rational complex
input codes, box bounds, and precisions. The claim for PR Cauchy names is
a schema in fixed PR definitions with supplied regularity hypotheses.
There is no internal quantification over arbitrary real numbers or
universal PR evaluator.

## Contents and status

| File or directory | Purpose |
| --- | --- |
| `zeta_functional_equation_ipra.tex`, `.pdf` | Complete human proof, bounds, arithmetic interpretation, and formalization plan. |
| `finite_contract.md` | Explicit finite approximation schedules and the rational residual checker specification. |
| `formalization_plan.md` | Object-theory interfaces, module order, proof obligations, and acceptance criteria. |
| `lean/` | Two **uncompiled interface drafts**, a recorded toolchain, and a status README. |
| `code/quantitative_bounds.py` | Exact rational checks of selected cutoff/error-budget instances. |
| `code/numerical_diagnostics.py` | Floating-point comparisons and finite algebra diagnostics. |
| `code/*.json` | Saved diagnostic outputs. |
| `code/build_pdf.py` | Rebuilds the report and records layout/reference checks. |
| `requirements.txt` | Pinned optional Python dependencies for the numerical diagnostic. |
| `provenance/` | Pinned repository information, inspected source copies, source hashes, and build metadata. |

**The analytic argument has not been formalized or kernel-checked in
Lean.** No Lean executable was available in the execution environment.
The two Lean drafts contain no added axioms or `sorry`, but neither
implements the full checker nor constructs its correctness derivation.
The required endpoint remains an actual term of
`Prf PRAAx [] (residualSentence compiledCheck)`.

The Python diagnostics are supporting checks. They are not certified
analytic enclosures, universal proofs, or iPRA proof objects. The enormous
primitive-recursive quadrature grids are specified and their bounds
checked; the numerical diagnostic uses a separate practical method.

## Reproduction

Run these commands from the extracted package root.

To rebuild the PDF, use Python 3 and an installed TeX distribution with
`pdflatex`, `pdftex`, `kpsewhich`, and the packages requested by the source:

```bash
python3 code/build_pdf.py
```

The script performs three LaTeX passes, writes temporary files under
`build/`, updates the root PDF and build metadata, and reports unresolved
references or overfull boxes.

To reproduce the exact arithmetic diagnostics, only Python's standard
library is required:

```bash
python3 code/quantitative_bounds.py --max-b 8 --max-p 12 --sample-b 4 --sample-p 20 --output code/quantitative_bounds_check.json
```

The separate numerical diagnostic uses the pinned `mpmath` and `sympy`
versions in `requirements.txt`:

```bash
python3 -m pip install -r requirements.txt
python3 code/numerical_diagnostics.py --dps 80 --output code/numerical_diagnostics.json
```

These commands overwrite the corresponding saved diagnostic outputs.
The recorded execution environment used Python 3.12.14; details are in
`provenance/environment.json`.
See `lean/README.md` for the proposed Lean checking workflow and its
explicitly incomplete status.

## Repository snapshot

The inspected ProveIt snapshot is commit
`c5093c20b5bffb0333fd42915b7bc858d5aa45cc`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/c5093c20b5bffb0333fd42915b7bc858d5aa45cc/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA>

Its recorded toolchain is `leanprover/lean4:v4.32.0`, and its Lake
configuration requests mathlib `v4.32.0`. The existing `pra_iff_native`
bridge supplies the intended final transfer into the native scalar
calculus. Source-reported build results for that repository are
distinguished from checks actually performed for this package.
