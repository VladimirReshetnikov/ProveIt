# Further Lean proof simplification: controller arithmetic and subset coverage

Checked source baseline: `VladimirReshetnikov/ProveIt` commit
`9f35798db4a63c25e435fca14d75931144657d7e`.
Final corpus and client refresh: `f00ba53b331833c6cb64707bd90e48489e5610f5`.
All 15 replay source/configuration inputs are unchanged between these pins.
The final corpus has 36 placed packets; the five initially incoming archives
were relocated into it, and eight additional reports were audited. An optional
prime-support suggestion was withdrawn when found among those additions.

Read `report.pdf` or rebuild `report.tex` with `validation.tex` alongside it.
The report contains the complete mathematical arguments, exact source targets,
comparisons with prior proposals, migration choices, and validation scope.

## Principal results

1. Every residue modulo T is a sum of a distinct residues for every 0<a<T,
   without coprimality. An explicit subset with at most one gap is constructed.
2. Consequently, an affine orbit of weights 1+C0*z modulo C0*T, with
   0<C0<T, covers every target using a subset of cardinality 1 through C0.
   This removes the arithmetic Boolean correction if the endpoint a=C0 is
   admitted. The newer physical-position safety lemmas already accept arbitrary
   subsets, and the maximum support count stays the same; their finite-update
   composition with this new endpoint has not been rebuilt.
3. The fixed CRT factors need annihilating powers; exact order remains
   indispensable at the auxiliary prime power and in the power-orbit injection.
4. Both independent exponents in the controller coefficient disappear in
   one residue ring. A checked fixed residue 706142772 modulo 11360848883
   is coprime to the modulus and proves the whole unit family.
5. A uniform all-exponent divisibility theorem reorganizes the principal-unit
   order proof without a zero/successor split. The supplied focused patch
   preserves all six old theorem signatures and changes 80 lines to 79.

The first-lift adapter and arbitrary-seed
translation theorem are companion options. Their overlapping benefits are
not added together as independent line savings.

## Contents

- `report.tex`, `validation.tex`, `report.pdf`: complete report and source.
- `lean/`: seven proof experiments; every final file has a successful receipt.
- `patches/prime-power-annihilator.patch`: focused patch, not automatically applied.
- `replacement/DiophantineConsistency/PrimePowerOrder.lean`: exact replacement
  source corresponding to that patch.
- `evidence/validation.json`, `evidence/logs/`: source hashes and final proof receipts.
- `evidence/source_manifest.json`: pinned project sources used by replay.
- `evidence/refactor_metrics.json`: exact helper-inclusive source comparison.
- `evidence/exclusion_inventory.json`, `evidence/exclusion_taxonomy.json`,
  `evidence/prior_report_headings.tsv`: audit of 23 placed packets and five
  incoming archives, with 74 TeX files/components and 1,295 searched text members.
- `evidence/freshness_refresh.json`, `evidence/refresh_delta_inventory.json`,
  and the refresh audit: final comparison with the expanded 36-packet corpus.
- `evidence/late_head_scope_addendum.md`: exact declarations supporting
  compatibility with the newer controller-placement and safety proofs.
- `evidence/` review notes: independent mathematical and novelty review.
- `scripts/replay.py`: focused compilation and axiom audit, without changing
  tracked repository files.
- `scripts/build_exclusion_inventory.py`: inert-data reproduction of the
  prior-proposal inventory; no earlier submitted code is executed.
- `scripts/check_examples.py`: exact small construction and finite-residue
  controls supporting inspection; these do not replace Lean proofs.
- `SHA256SUMS`: checksums for packaged files other than the checksum list itself.

## Replay the Lean checks

Use a checkout at either recorded pin with its pinned Lean 4.32.0 toolchain and
mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` available:

```bash
python3 scripts/replay.py /path/to/ProveIt
```

The script verifies the accepted revision and relevant source hashes. It builds only
the named prerequisites, compiles the proof experiments in a local isolated
directory, checks patch applicability, and compiles the replacement under
the actual module name followed by the unchanged focused Checks source.
It does not apply the patch. New replay receipts go into `replay-results/`;
the packaged original receipts remain unchanged.

The prototype for whole-Gamma transport keeps K symbolic and assumes only
the three literal-kernel residues already proved in the repository. The
actual production endpoint and its callers were not rebuilt for that idea.
The affine adapter reuses freshly compiled original coordinate modules but
deliberately changes the cardinality bound from a<C0 to a<=C0. No whole-project
build, automatic removal of physical controller terms, or final consistency
equivalence is claimed.

## Rebuild the PDF

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Interpret the evidence

Earlier ideas are treated as available even when the repository marks them
pending or deferred. Novelty is relative to the reviewed proposal corpus,
not a claim of mathematical priority. Counts of searched text members do
not mean every word of each embedded source snapshot was read.

All final audited Lean declarations depend only on the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`, or on no axioms. Timing
receipts came from a shared environment and are not performance benchmarks.
The only measured integrated line comparison is the focused 80-to-79-line
order-module replacement; all other deletion opportunities depend on the
choice of compatibility APIs and downstream integration.
