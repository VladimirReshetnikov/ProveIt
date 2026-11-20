# Continuous mathematics in iPRA

Research package prepared for Vladimir Reshetnikov, 20 November 2026.

Start with `continuous_mathematics_in_ipra.pdf`. Its LaTeX source is
`continuous_mathematics_in_ipra.tex`, with chapter fragments in `sections/`.

## Main content

The report develops three complementary interpretation levels:

1. Fixed primitive recursive approximation families with object-iPRA numerical contracts.
2. Internally quantified program-code sorts with arithmetical totality and coherence predicates.
3. Semantic adequacy in ordinary completed metric spaces.

It supplies full human arguments for relational regular names and diagonal
completion; the continuous extension universal property; quantitative function
objects; continuous formula evaluation and approximate preservation between
metric structures; local gluing with positive-margin chart certificates; an
actual Euler ODE construction with a convergence schedule, integral equation
and uniqueness; and a guarded polygonal Cauchy transform with Taylor and
derivative estimates.

The code-totality discussion distinguishes a single terminating evaluation
from the batch or iteration contracts needed by variable-length computation.

## Formalization status

**The new analytic theorems are not delivered as kernel-checked Lean proofs.**
The user-requested Lean outline consists of concrete definitions, target
propositions, a module plan, and a small object-judgment adapter. All Lean files
are explicitly uncompiled in this environment. Main proof obligations are
defined as propositions rather than filled by `sorry` or asserted as axioms.
Host specifications using Lean functions do not themselves certify primitive
recursiveness or prove anything in object iPRA.

The upstream source audit is pinned to:

`5f3be02388442f16487d2dc5c2529961dd783d2b`

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

The upstream toolchain file specifies Lean `v4.32.0`. Upstream modules were
inspected, not rebuilt here. The one-sorted equational `SetoidInterpretation`
interface already exists; many-sorted relational adaptation remains explicit
new formalization work.

## Contents

| Path | Purpose |
|---|---|
| `continuous_mathematics_in_ipra.pdf` | Complete report |
| `continuous_mathematics_in_ipra.tex`, `sections/`, `sources/references.tex` | Rebuildable LaTeX source |
| `lean/ObjectContracts.lean` | Actual `Prf PRAAx` structural adapters, uncompiled candidate |
| `lean/RelationalNamesBlueprint.lean` | Trace, totality, regular-name, completion and batch interfaces |
| `lean/CategoryModelBlueprint.lean` | Metric completion and continuous formula definitions/targets |
| `lean/AnalyticBlueprint.lean` | Rational Euler and complex-kernel definitions/targets |
| `lean/FORMALIZATION.md` | Exact formalization obligations and dependency order |
| `code/continuous_reference.py` | Exact rational model/ODE/Cauchy programs |
| `code/validate.py` | Reproducible representative checks against independent enclosures |
| `code/plot_validation.py` | Figure generation from the validation receipt |
| `validation/results.json`, `validation/status.json` | Honest machine-readable validation/status records |
| `sources/` | Source audit, upstream manifest and references |
| `SHA256SUMS.txt` | Checksums of packaged files |

## Reproduce

The numerical checks require Python 3.10 or later and its standard library:

```sh
python3 code/validate.py
```

The figure additionally requires Matplotlib:

```sh
python3 code/plot_validation.py
```

Rebuild the report using a normal TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error continuous_mathematics_in_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error continuous_mathematics_in_ipra.tex
```

For the Lean outlines, place the files in a checkout of the pinned ProveIt
revision and run `lake env lean` on each file. This is a proposed replay command,
not a report that it succeeded here. Implement the listed obligations and
finish with the repository's actual object-theory endpoints and axiom audit.

## Scope

Finite nets and positive margins are supplied effective data, not consequences
of arbitrary classical compactness. Equality of named reals is a formula, not
a decidable test. The complex construction is a Cauchy transform, not a proof
of the full Cauchy integral formula or residue theorem. The ODE theorem has
explicit field bounds, Lipschitz moduli and a guarded tube. No claim is made
that all classical real numbers or arbitrary topological spaces have these
computational presentations.

The reference tests check selected instances and implementation consistency.
Their success does not establish the universal mathematical theorems or
replace completion of the Lean proof obligations.
