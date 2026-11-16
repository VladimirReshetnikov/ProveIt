# Four exact metrics in intuitionistic primitive recursive arithmetic

This package proves precise local exact-solution forms of the **Schwarzschild,
Reissner–Nordström, Kerr, and Kerr–Newman metrics**. It contains the complete
human-readable LaTeX article, its compiled PDF, exact arithmetic verification
programs and outputs, and an explicit Lean formalization outline.

## Start here

- `paper/four_metrics_ipra.pdf`: the complete mathematical argument.
- `paper/four_metrics_ipra.tex`: editable LaTeX source.
- `paper/verification_summary.tex`: included verification summary.
- `lean/README.md`: formalization status and completion order.
- `certificates/suite_results.json`: final standard-library replay.
- `certificates/independent_suite_results.json`: independent symbolic replay.

## What is proved

With signature `(-,+,+,+)`, define

```
s = 1 - x^2
Sigma = r^2 + a^2*x^2
Delta = r^2 - 2*m*r + a^2 + q^2
p = dt - a*s*dphi
b = (r^2+a^2)*dphi - a*dt

g = -(Delta/Sigma)*p^2 + (Sigma/Delta)*dr^2
    + (Sigma/s)*dx^2 + (s/Sigma)*b^2
A = -(q*r/Sigma)*p
```

The literal arithmetic theorem quantifies over natural-number codes of the five
rational inputs. Under valid coding and `Sigma*Delta*s != 0`, the exact inverse,
determinant, Einstein–Maxwell, source-free Maxwell, and Bianchi identities hold.
The human iPRA proof specifies the primitive recursive operations and the
quantifier-free induction invariants connecting zero polynomial coefficients
to the uniform statement at every guarded rational input.

The main geometric calculation is a general radial-function Ricci lemma. It
reduces Einstein–Maxwell in the chosen rotating ansatz to

```
Delta'' = 2
r^2 - a^2 + Delta - r*Delta' = q^2
```

and derives the displayed quadratic Delta within the polynomial ansatz. Setting
`q=0`, `a=0`, or both yields the other three metrics exactly.

Further proved results include rational ingoing and stereographic charts,
Lorentz signature at the axes and at `Delta=0`, an explicit rational flat
Cartesian pullback and Kerr–Schild form, local Killing-horizon identities,
surface gravity, stationary-limit equations, Ricci-square and Kretschmann
invariants, and explicit equatorial curvature blow-up bounds.

The constructive-real interpretation is a **conditional scheme** for externally
fixed primitive recursive names, with explicit regularity, magnitude,
positivity, and denominator-apartness contracts. Externally true contracts
are not silently assumed to be iPRA-provable.

## Formal verification status

The **human mathematical proof and exact executable checks are supplied**.
The new Lean files are **uncompiled outlines**, with complete core definitions
and explicit outstanding proposition-valued targets. There is no completed
Lean term proving the full object-language theorem `Prf PRAAx [] statement`.
No `sorry` or new axiom is used to present that missing result as established.
Conditional assembly theorems remain conditional.

The packet does not assert global stationary black-hole uniqueness, maximal
analytic extension, global event-horizon identification, stability, or a
physical-collapse theorem. Those are separate from proving that the explicit
metric and field satisfy the local field equations.

## Reproduce the exact checks

The default suite needs Python 3 and **no third-party packages**:

```sh
python3 code/run_all.py
```

Checks remain active with Python optimization enabled:

```sh
python3 -O code/run_all.py
```

For the independent symbolic comparison, install SymPy and run:

```sh
python3 code/run_all.py --sympy
```

The six standard-library programs execute in isolated subprocesses. The final
suite passed 491 positive exact checks, including five arithmetic controls, and
correctly rejected four deliberately nonzero residuals. The independent SymPy
run passed, and all 48 stored Ricci, field, and Maxwell-density components
agreed exactly. The JSON and logs record the actual runs.

The `verify_stdlib.py` checker has 10,297 source bytes and 3,773 bytes under
reproducible gzip level 9 (`mtime=0`). These are size observations for the
readable principal checker, not a minimality claim. See `code_sizes.json` for
all program sizes and hashes.

## Rebuild the PDF

With a standard LaTeX installation providing the packages listed in the source:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error four_metrics_ipra.tex
```

If `latexmk` is unavailable, run `pdflatex` at least twice to resolve references
and the contents. The PDF was rendered and visually checked before delivery.

## Lean integration and provenance

The inspected ProveIt snapshot is
`87ccad4659b63acdce75540d17a69d799bbd25ad`:

https://github.com/VladimirReshetnikov/ProveIt/tree/87ccad4659b63acdce75540d17a69d799bbd25ad/Logic/PrimitiveRecursiveArithmetic

It identifies Lean/mathlib v4.32.0. Its checked `ConciseIPRA` core is the intended
object-language destination. Four inspected source files and their upstream
license are included under `lean/upstream_inspected/`; their exact Git blob
hashes are recorded in `SOURCES.json`. They are provenance excerpts, not the
whole transitive Lean build. The proof does not assume the correctness of
unverified research packets filed elsewhere in the repository.

Primary comparison sources:

- Adamo and Newman, *The Kerr–Newman metric: A Review*, arXiv:1410.6626v2.
  https://arxiv.org/abs/1410.6626
- Frolov, Krtouš and Kubizňák, *Black holes, hidden symmetries, and complete
  integrability*, arXiv:1705.05482v3.
  https://arxiv.org/abs/1705.05482

All metric and tensor formulas are independently derived and explicitly
verified in this package. No novelty claim is made for the classical solutions.
