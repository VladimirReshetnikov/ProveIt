# New structures for shorter Lean proofs

Prepared for Vladimir Reshetnikov, 26 October 2026.

## Read first

`report.pdf` is the full research report; `report.tex` is a complete standalone LaTeX source; `validation.tex` also preserves its validation section separately.
The baseline is ProveIt commit `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`, Lean 4.32.0,
and mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`.

The four additional directions are integer-period closure, algebraic descent of the two-radicand
polynomial identity, canonical helical band coordinates, and construction from shared edge fields.
Earlier ideas in all eighteen audited proposal packets are treated as already applied.

## Scope

The ZIP is a review packet. No patch was pushed or applied to the user's repository.
The exact compiler scope and source metrics are in `evidence/validation-summary.json` and the report.
Generic checked theorem cores are not a claim that all production clients were rebuilt.
No measured total saving is asserted for the two architectural geometry proposals.

## Contents

- `lean/Periodicity.lean`: original and replacement helix/seam proofs and axiom comparisons.
- `lean/RefinedPairAlgebraic.lean`: algebraic combiner identity and integer evaluation.
- `lean/HelicalCoordinatesCore.lean`: the successfully checked signed-address uniqueness, normalization and origin criterion.
- `lean/HelicalCoordinates.lean`: includes the prepared finite band equivalence, whose full compiler replay did not finish.
- `lean/EdgeFieldsCore.lean`: successfully kernel-checked, self-contained generic row/grid representation and inverse laws.
- `lean/EdgeFields.lean`: additionally includes successfully kernel-checked exact initializer and unrestricted literal step-pattern bridges. This complete standalone module passed; production clients were not rebuilt.
- `patches/`: reviewable proposed production edits.
- `audit/`: exclusions, archive-member hashes and independent mathematical review.
- `evidence/`: logs, source manifests, source metrics and validation receipt.
- `dependencies/`: exact authenticated polynomial dependency sources and any explicitly recorded validation-only import adjustment.

## Replay

Use a checkout of the pinned ProveIt revision with its dependencies available.
From that checkout, first build the relevant shared dependency:

```sh
lake build Diophantine.Common.RefinedRelationCombiningPolynomial
```

Then run each prototype through that checkout's environment, using the absolute path to this packet:

```sh
lake env lean /absolute/path/to/packet/lean/Periodicity.lean
lake env lean /absolute/path/to/packet/lean/RefinedPairAlgebraic.lean
lake env lean /absolute/path/to/packet/lean/HelicalCoordinatesCore.lean
lake env lean /absolute/path/to/packet/lean/HelicalCoordinates.lean
lake env lean /absolute/path/to/packet/lean/EdgeFieldsCore.lean
lake env lean /absolute/path/to/packet/lean/EdgeFields.lean
```

The periodicity and coordinate files import mathlib only. The edge-field core needs no external
imports; its larger arithmetic example file imports Lean core Omega. The algebraic prototype additionally needs the ProveIt HTP modules. That proposal was NOT compiler-validated: the dependency build stalled before the new module was reached.
If reproducing the isolated dependency build rather than a normal project build, inspect the
explicit dependency-source and import-adjustment receipts. Do not mistake an import-only change
for a proof assumption.

`python3 scripts/verify_artifacts.py` checks the delivered bytes against `SHA256SUMS`.
To rebuild the report, run XeLaTeX twice from this directory:

```sh
xelatex -interaction=nonstopmode -halt-on-error report.tex
xelatex -interaction=nonstopmode -halt-on-error report.tex
```

XeLaTeX, Latin Modern fonts, DejaVu Sans Mono, and standard TeX packages listed in the preamble
are required. The source includes Lean Unicode and mathematical typesetting.

## Integration order

Apply the small period patch and the algebraic replacement first, then rebuild focused production
checks. Introduce the helical coordinate interface across multiple clients before measuring its
net source savings. For edge fields, define fields independently and prove literal tuple equality;
do not use `grid_eq_of_matching` circularly to hide the matching proofs being replaced.
Preserve unrestricted `cfg`/`q` interfaces, actual rail colors, all 942-tile bindings, the signed
address convention, finite-height separation and marker semantics.
