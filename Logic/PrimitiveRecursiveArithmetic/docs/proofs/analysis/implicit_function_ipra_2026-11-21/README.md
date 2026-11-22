# A quantitative constructive implicit function theorem in iPRA

Prepared for Vladimir Reshetnikov, November 21, 2026.

The report proves a finite-dimensional C1 implicit function theorem for
fixed primitive recursive presentations with certified Taylor and derivative
continuity moduli. It supplies an explicit neighborhood, a primitive recursive
solution evaluator, uniqueness, a residual error bound, a parameter Lipschitz
bound, a derivative evaluator, and explicit moduli for differentiability and
continuity of the derivative.

The mathematical result is a first-order theorem schema for fixed PR programs,
with universal numerical certificate hypotheses. A positive determinant bound
provides the conditioning witness through a bounded rational construction.
The theorem does not quantify internally over all PR programs or infer
primitive recursive moduli from bare qualitative continuity.

## Start here

- **paper/implicit_function_ipra.pdf** — complete report.
- **paper/implicit_function_ipra.tex** and **paper/sections/** — complete LaTeX source.
- **lean/FiniteCore.lean** — checked finite arithmetic and algebra lemmas.
- **lean/BLUEPRINT.md** — full formalization plan and required representations.
- **code/implicit_solver.py** — exact-rational finite algorithm and examples.
- **code/validate.py** — reproducible targeted validation.
- **validation/python_validation.json** — deterministic validation results.
- **references/proveit/** — source audit and selected commit-pinned reference modules.

## Main construction

Normalize the original equation as H = A F, where the rational matrix A has
an explicit rational inverse. On a product box with vertical radius r, require

    ||I - D_y H|| <= 1/2
    ||D_x H|| <= M
    ||H(a,b)|| <= r/4
    M * alpha <= r/4.

Set s to the least nonnegative integer with 2r <= 2^s. At precision k, start
at b and take exactly k+s+4 steps. Evaluate H and round down to a dyadic grid
at precision k+5, then clip each result to the rational vertical box.
The resulting step error is at most epsilon = 2^(-(k+4)).

The finite comparison proof gives

    ||g_hat(x,k) - g_hat(x',l)||
        <= 2M ||x-x'|| + 3 epsilon_k + 2 epsilon_l     (k <= l).

The direct residual bound is

    ||H(x,g_hat(x,k))|| <= 4 epsilon_k.

These estimates construct a coherent name without invoking existence of the
limit of an arbitrary Cauchy sequence. The derivative is computed by a finite
Neumann sum with an explicit coefficient-error allowance.

## Verification status

| Component | Status |
| --- | --- |
| Full quantitative C1 theorem and iPRA induction audit | Human-readable proof in the report |
| Finite contraction arithmetic, Boolean trace bound, iteration concatenation, vector Neumann identity | Compiled Lean 4.32.0 proofs, using bundled Std |
| Full implicit function theorem in Lean | Detailed outline; not completed |
| Full object-iPRA proof term | Detailed integration plan; not completed |
| Exact-rational implementation | Validated on 4,680 finite traces and additional targeted checks |
| Imported ProveIt reference modules | Source-inspected at the pinned commit; not rebuilt in this package |

The checked Lean file contains no sorry placeholders or user-declared axioms.
The recorded host-Lean dependency audit includes propext and Quot.sound, and
does not include Classical.choice. This is not a claim that arbitrary Lean
proofs automatically belong to iPRA.

All 1,317,978 computational assertions passed using integers and Fraction.
The tests establish behavior on their stated finite domains; universal
mathematical certificates are proved in the report, not by sampling.

## Reproduce

Python validation requires only the standard library:

~~~sh
python3 code/validate.py
~~~

Lean uses the pinned toolchain in the project:

~~~sh
cd lean
lake build
~~~

With a normal LaTeX distribution:

~~~sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error implicit_function_ipra.tex
~~~

Alternatively run pdflatex twice from the paper directory. The included
figure is already built. To regenerate it, install Matplotlib and run:

~~~sh
python3 code/make_figure.py
~~~

Floating point is used only for drawing the figure, never in validation
pass/fail checks. The downloaded Lean compiler and generated build caches
are intentionally not part of the archive.

## ProveIt provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: d36b35eed5bd01af4ade66bf539622495813ccc8

The source audit distinguishes internal runtime-index object proofs from
externally indexed families of proof terms. The selected reference sources
are not a standalone build target and do not include their transitive imports.
Their original contents are preserved; the manifest records their blob hashes
and exact URLs. The standalone Lean target depends only on Std.
