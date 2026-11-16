# Certified Finitary Presentations for Mathematics in iPRA

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `paper/ipra_embedding_framework.pdf` - the 40-page human-readable report.
- `paper/ipra_embedding_framework.tex` - master LaTeX source.
- `paper/sections/` - editable section sources.
- `THEOREM_LEDGER.md` - concise status of every main framework claim.
- `lean/LEAN_PLAN.md` - dependency-ordered path to embedded Lean proofs.

## Main contribution

The report develops a **Certified Finitary Presentation (CFP)** framework for
turning mathematical arguments into intuitionistic primitive recursive
arithmetic. Its reusable core is:

1. fixed natural-number codes or fixed primitive-recursive evaluator schemas;
2. finite observations and explicit precision transformers;
3. totalized operations with Boolean domain/apartness guards;
4. bounded traces with quantifier-free Boolean invariants;
5. finite nets, nested isolating certificates, and checked search bounds;
6. a final object-language derivation in `PRAAx`, transported only afterward
   through the existing `pra_iff_native` bridge.

The paper gives developed proofs of the finite-trace reflection theorem,
Boolean-fold compilation, fixed-precision/all-precision discipline, robust
overlapping branches, exact branching under a gap, finite-net transfer,
approximate witness search, nested-ball regular names, and the equivalence of
height bounds with complete finite lists.

## Difficulties addressed

The framework gives a common resolution for recurring proof-packet problems:

- unbounded-precision induction -> finite query tables at a free precision;
- exact boundary selection -> overlapping branches or positive gaps;
- abstract compactness -> primitive-recursive finite nets and refinement;
- root/eigenvector/axis choice -> projective or isolating data first;
- higher-type functions and measures -> fixed evaluator schemas or finite
  approximants with moduli;
- ambient Lean results -> explicit `Prf PRAAx` proof obligations;
- Diophantine finiteness -> separate finite verifier from height/covering
  certificate production;
- ineffective analytic constants -> explicit analytic-input certificates and
  correct quantifier order.

The report also proves why several stronger interfaces cannot be obtained by
better encoding: no total universal PR evaluator exists; cardinality bounds do
not yield search cutoffs; and exact sign/branch selectors can imply LLPO or
related principles.

## Exact executable companion

`code/certificate_kernel.py` uses only integers and `fractions.Fraction`. It
checks:

- a bounded recurrence trace and invariant;
- a robust overlapping branch;
- finite-grid residual minimization for `x^2 - 2`;
- finite regularity tests for a dyadic `sqrt(2)` name;
- height-bound/list conversions.

Run:

```bash
cd code
python3 -m unittest -v test_certificate_kernel.py
python3 certificate_kernel.py ../examples/framework_certificate.json
```

The delivered run passes all 9 unit tests. These are independent semantic
checks, not substitutes for embedded iPRA proofs.

## Lean status

- `lean/FiniteTraceSemantic.lean` is an ordinary Mathlib-level prototype of
  the trace theorem and finite-list height argument.
- `lean/IPRAObjectLanguageBlueprint.lean` imports the actual `ConciseIPRA`
  interfaces and records the proposed `PRTraceSystem`, formula design, and
  exact proof path.
- The generic embedded `Prf PRAAx` reflection theorem has **not** yet been
  constructed or compiler-checked.
- Lean/Lake was unavailable in the artifact-building environment, so neither
  Lean file was compiled here.

This distinction is deliberate: the archive does not present an ambient Lean
theorem as an iPRA derivation.

## Rebuild and validate

A standard TeX Live installation with `latexmk` is sufficient:

```bash
bash build.sh
```

The script runs Python tests, validates the JSON certificate, compiles the PDF,
and performs PDF preflight/text checks. The delivered PDF has 40 pages,
embedded fonts, no unresolved `??` references, and no replacement glyphs. It
was rendered to PNG pages and visually inspected for clipping and overlap.

## Repository baseline

Inspected repository:

- `https://github.com/VladimirReshetnikov/ProveIt`
- main commit: `7d492fbfc5fee3b2b9dec0b2623b0b82effe05f2`

The source audit is in `metadata/source_audit.md` and in Appendix B of the
paper. The external repository was inspected read-only; no repository change
is implied.

## Archive contents

- `paper/` - LaTeX source and compiled PDF.
- `lean/` - semantic prototype, object-language blueprint, completion plan.
- `code/` - exact reference checker and tests.
- `examples/` - reproducible JSON certificate.
- `metadata/` - difficulty matrix, framework schema, source audit, validation
  summary.
- `verification/` - observed test output and PDF inspection/preflight reports.
- `MANIFEST.sha256` - checksums of all other delivered files.
