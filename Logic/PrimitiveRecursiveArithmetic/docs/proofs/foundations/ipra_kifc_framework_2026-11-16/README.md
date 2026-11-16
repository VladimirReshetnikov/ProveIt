# Kernel-Integrated Finitary Contracts for iPRA — second edition

This archive develops **KIFC**, a proof-producing framework for translating
fixed, finite mathematical constructions into derivations in intuitionistic
primitive recursive arithmetic (iPRA). It is pinned to ProveIt commit
`7c1f2594117c15a980d24300593d625722812768` (16 November 2026).

The target of the framework is not merely a semantic Lean theorem or a tested
program. A completed public result has the embedded object-language type

```text
Γ ⊢[PRAAx] φ
```

for an explicit iPRA formula `φ`.

## Main architecture

A theorem-specific construction is normalized to six node classes:

1. exact algebra;
2. Boolean decision;
3. bounded search;
4. certified iteration;
5. finite relational choice;
6. stable or guarded observation.

A reverse pass fixes precision, fuel, margins, and finite-use demands before
induction. A forward pass executes one query-specialized primitive-recursive
state machine. Its local object-level certificates are composed through
substitution, simultaneous cut, equality transport, and quantifier-free
induction. No total object-level evaluator for arbitrary primitive-recursive
codes is assumed.

Non-unique outputs remain finite relations until uniqueness, a separation gap,
a shrinking estimate, or observer stability justifies erasing the choice. Deep
inputs such as height bounds, zero-free regions, root-separation estimates, and
finite covers are treated as producer certificates with primitive-recursive
verifiers rather than silently imported compactness principles.

## Additions in this edition

Compared with the 15 November framework packets, this edition adds:

- a bounded-existential normal form and constructive least-witness extraction;
- a corrected finite-fold reflection proof whose only induction invariant is
  quantifier-free;
- direct reuse of the checked `IPRADerivations.Core.Search` least-zero backend;
- a complete human proof of retained classical-to-intuitionistic transfer;
- a de Bruijn-aware executable reference for the negative translation;
- a module-by-module integration map for the current `ConciseIPRA` and
  `IPRADerivations` APIs;
- explicit separation of source-complete adapters from placeholder-bearing
  Lean blueprints.

## Contents

- `paper/ipra_kifc_framework.pdf` — the compiled 72-page report.
- `paper/ipra_kifc_framework.tex` and `paper/sections/*.tex` — LaTeX source.
- `lean/KIFC/*.lean` — kernel-facing adapters and formalization blueprints.
- `lean/FORMALIZATION_PLAN.md` — dependency order and completion gates.
- `reference/kifc_reference.py` — exact finite reference algorithms.
- `reference/negative_translation_reference.py` — syntax, substitution,
  retained-fragment classification, and finite-model checks for the negative
  translation.
- `reference/test_*.py` — 23 unit and property tests.
- `examples/*.json` — deterministic and relational contract graphs and a
  dead-end viability fixture.
- `metadata/THEOREM_LEDGER.md` — claim-by-claim status ledger.
- `metadata/INTEGRATION_MAP.csv` — current repository service map.
- `metadata/difficulty_matrix.csv` — obstacle, resolution, and producer audit.
- `metadata/SOURCE_AUDIT.md` — pinned source paths and provenance.
- `metadata/proof_status.json` — machine-readable verification boundary.
- `validation/` — test, schema, PDF, Lean-source, build, and visual-audit
  records.
- `MANIFEST.sha256` — checksums for all distributed files.

## Verification status

- **Human mathematics:** the generic finite theorems and barrier arguments are
  developed in the report. The ledger distinguishes unconditional theorems,
  conditional producer interfaces, inherited checked components, and open
  application-specific obligations.
- **Python:** all 23 tests pass. They exercise folds, search, traces, demand
  propagation, viability, stable observers, shrinking budgets, guarded
  selection, exact rational bisection, height/list conversion, de Bruijn
  substitution, quantifier-free preservation, retained syntax, and finite-model
  equivalence of the negative translation.
- **PDF:** compiled, preflighted, rendered at 180 DPI, and visually audited over
  all 72 pages.
- **Lean:** Lean and Lake were unavailable in the artifact environment, so no
  new-module build is claimed. The source-complete kernel adapter subset has no
  intentional proof holes. `lean/KIFC/RetainedTransferBlueprint.lean` is
  deliberately marked as a blueprint and contains 18 explicit `sorry`
  placeholders delimiting the remaining kernel-checked implementation.
- **Inherited ProveIt results:** tied to exact files and the pinned commit in the
  source audit. They were inspected through repository source and recorded
  build/axiom-audit evidence, not independently rebuilt here.

## Reproduction

From the artifact root:

```sh
./build.sh
```

The script runs the Python tests, validates JSON against the framework schema,
scans the Lean sources for placeholders, compiles the report with `latexmk`,
runs PDF inspection and preflight tools, and refreshes the checksum manifest.
It expects Python 3, `jsonschema`, a TeX installation with `latexmk`, Poppler's
`pdfinfo`, and the PDF utilities installed in this environment.

The intended repository-side Lean completion begins with
`KIFC/KernelCore.lean`, Boolean reflection and bounded folds, the checked-search
adapter, and loop certificates; finite relational viability and retained proof
translation follow only after those foundations compile and pass axiom audits.
