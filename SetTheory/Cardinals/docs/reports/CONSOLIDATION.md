# Research-report consolidation, 29 September 2026

Four maintained reports have been consolidated into two articles, representing
five original manuscripts. The collection now contains **111 reports**, with
**19** in ordinals and order types. The catalogue and the repository, SetTheory,
and Cardinals landing pages agree on these counts.

## Selection and boundaries

This pass used the collection catalogue and its earlier duplicate-review record
to identify unresolved overlap, then compared the manuscripts, hypotheses,
proof routes, notation, implementations and audits in the two clusters below.
The existing duplicate review had kept these reports separate because their
proofs differed. Here the common statements are consolidated while the distinct
arguments remain explicit alternatives or extensions.

This is an editorial and mathematical comparison of these clusters, not a fresh
correctness review of all 111 reports. The friendly-order-type reports remain
separate: their finite formula overlaps, but their transfinite continuations
and certificate frameworks need a dedicated synthesis. Other previously
documented pairs with incomparable hypotheses or distinct conjectures retain
their existing dispositions. The separate transseries intake advancing on
main was incorporated without editing its material.

## Minimal infinitary ordinal sum

Canonical article: [PDF](ordinals-and-order-types/ordinal-arithmetic/lipparini-minimal-infinitary-sum/article/explicit_ordinal_sum.pdf),
[source](ordinals-and-order-types/ordinal-arithmetic/lipparini-minimal-infinitary-sum/article/explicit_ordinal_sum.tex),
[merge concordance](ordinals-and-order-types/ordinal-arithmetic/lipparini-minimal-infinitary-sum/MERGE_NOTES.md).

`lipparini-minimal-operation-formula` is absorbed into
`lipparini-minimal-infinitary-sum`. Both propose the same three-case answer to
Lipparini's Problem 6.2 for arbitrary-ordinal, omega-indexed inputs. The common
formula, imported weaker-operation theorem, correction rules and constant
values are stated once. The profile-rank/absorption argument and the
corrected-block/threshold-interpolation argument are both retained, including
the latter's finite-part restoration. Its equality criterion, cardinality
result, block-rank theorem, examples and negative controls remain.

The finite-cap models are identified under the explicit shift
`(n,E) -> (n+1,{t+1:t in E})`; the alternative predecessor proof is retained.
The second arithmetic implementation lives under `code/block/`, avoiding a
module-name collision. Its historical evidence and source audits are unchanged.
The unified PDF has **32 pages**.

## Finite-alphabet transfinite words

Canonical article: [PDF](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared/article.pdf),
[source](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared/article.tex),
[merge concordance](ordinals-and-order-types/transfinite-words/order-types-below-omega-squared/MERGE_NOTES.md).

`finite-alphabet-transfinite-words` is absorbed into
`order-types-below-omega-squared`, which already represented two original
manuscripts. The shared finite-alphabet setup and height-two formula are stated
once. The finite-height theorem, canonical atom recurrence, protected-separator
induction, growth bounds and symbolic cycle implementation are integrated.
The selected-periodic-family classification, universal-only exception,
exact-length strata, canonical token algorithm, and both original lower-bound
routes remain. The second implementation lives under `code/heights/`.

The notation explicitly distinguishes the full language `V_k(P)` from the
selected-family language `W(P,F)`. The general finite-height theorem does not
classify arbitrary selected families at greater heights, nor establish the
all-height union. The elementary lower-bound route removes the natural-product
import for the original height-two main theorem only. Two sentences now say
that an element is dominated by a recurrent letter; the element need not itself
recur when the periodic representative repeats only maximal generators.
The unified PDF has **45 pages**.

## Preservation and fresh verification

The editorial baseline is Git commit `5804c7aff`; this is not an author-supplied
formal-project pin. Old directories contain redirects, and their former sources
and PDFs remain recoverable in Git. All 69 and 94 original destination labels
survive. Every incoming label has a documented destination (66 and 58,
respectively). There are 251 unique labels across the two unified documents.
All 27 relocated supporting files are byte-identical to the baseline, as are
the unmoved supporting files. Retired build wrappers are superseded by the
canonical build scripts. Historical audit dates and recorded results are kept.

Run the structural and cross-implementation check from the repository root:

```sh
python -B scripts/check_report_consolidation.py
```

The [checker](../../../../scripts/check_report_consolidation.py) verifies label
preservation, concordance completeness, reference resolution, evidence identity,
retirement and redirect status, catalogue counts and PDF paths. It also compares
the two ordinal implementations on 5,000 certified profiles with deterministic
seed `20260929`, including hereditary nested exponents.

All four source suites were rerun on scratch copies, preserving delivered
evidence. The fresh JSON receipts are in
[`consolidation-checks/2026-09-29/`](consolidation-checks/2026-09-29/).

| Suite | Fresh result |
|---|---|
| Ordinal profiles | PASS: 734,869 counted checks, including 912 finite ranks |
| Corrected blocks | PASS: 20,000 comparable pairs, 40,000 formula comparisons, 24,916 block comparisons, 994 finite states and 122,738 strict comparisons |
| Guarded words | PASS: 3,240,040 assertions, including the required negative controls |
| Finite-height words | PASS: 24 alphabet posets, 72 atom posets, 87 independent and 64 brute ideal-count agreements, 1,922 marker pairs, 10,000 equal-block pairs, 18,000 separator pairs, 625 singleton pairs and two absorption checks |

These categories overlap; they are not a combined independent-test total.
Reproduce from a scratch copy of each canonical report directory:

```sh
# Ordinal report
python code/verify.py --output checks/fresh.json
python code/block/verify.py --seed 20260919 --trials 20000 --output data/block/fresh.json

# Transfinite-word report
python code/verify.py --output-dir fresh-guarded
python code/heights/verify.py --out fresh-heights
```

Both articles and the 29-page catalogue were rebuilt with three serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes per final source.
Final logs have no unresolved references, LaTeX/package warnings or overfull
boxes. Rendered pages were reviewed, including the integration boundaries,
tables and proof maps. The catalogue's directory table and Hankel formula
layout were adjusted to remove overflow; its p-adic bookmark has a text form.

These checks establish preservation, finite implementation agreement and
rendered-document consistency. They do not prove the transfinite theorems,
constitute Lean/Rocq verification, refresh the literature searches, or establish
priority or peer review. The original scope qualifications remain explicit.
