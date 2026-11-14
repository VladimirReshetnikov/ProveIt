# PA consistency Turing machines: comparison and reduction investigation

**The requested machine with fewer than 196 working states was not obtained.**
This archive does not contain a table represented as a verified solution of
that strict state bound. It contains the complete comparison, new positive
same-size work, explicit failed candidates, and reproducible evidence.

## Read first

- `report.pdf`: the typeset report.
- `report.tex`, `outcome.tex`, `archive_table.tex`, `search_results.tex`, and
  `disequality_parity.tex`: its complete LaTeX sources.
- `comparison/COMPARISON_CURRENT.md`: the detailed archive-by-archive audit.
- `verification/zero_jump_machine/newwork.md`: the new 196-state result and
  the exact reason the attempted 195-state fold fails.

The source snapshot is VladimirReshetnikov/ProveIt commit
`1fe9b29810bfe3d0e507146d65f6b97692e7444a`. The manifest pins all 24 incoming
ZIPs and the recursively inventoried members. None of the original remote
repository was modified.

## Main results

| Item | Result and limitation |
|---|---|
| Supplied archive census | 24 top-level ZIPs, 37 distinct nested ZIP bodies; 27 designated U208 presentations form 20 rooted graphs. |
| Selected 196-state catalogue | 18 distinct rooted graphs: 14 baseline/report-positive, 2 experimental, 2 rejected blank-halting controls. |
| Supplied 195-state tables | Five byte forms, four graph classes, all rejected or diagnostic. |
| New zero-jump machine | 196 states; 4,959 uniform instruction contracts pass; exact blank startup in 58,402 transitions. |
| New attempted 195-state fold | Rejected: source26 goes to the wrong successor and increments register6. Both an isolated frame and the actual blank trace reproduce the error. |
| Joint jump-action products | 936 including baseline; 671 modified combinations pass instruction contracts, 264 fail. No saving in the specified helper-fold search. Startup is not certified for all 671. |
| Base-eight parity integration | 202-state literal runtime, 4,062 source sites, 5,205 uniform contracts pass; no certified blank initializer and no sub-196 result. |
| Disequality parity recoding | Mathematical calculus/acceptance transport and exact emitter witnesses; no completed tape machine. |

The new machine is `verification/zero_jump_machine/machines/zerojump196.tm`.
It changes native PA196 row `27/1` from `0 L 40` to `1 R 21`. At source site26,
the complete source invariant forces logical register6 to be zero, so the
decrement implements the old forward jump. Its table SHA-256 is:

`2c1a736399e0f32304ed18d6a439dc8d4fdd82f2ad103cdfc6851c0f4ae1e4af`

The result is a relative simulation of the original source search. It
transfers an established consistency characterization through that simulation;
it does not add a new closed Lean theorem of the PA-internal biconditional.

## Reproduce the main checks

Use Python 3.10 or later. The default verification uses only the standard
library. From this directory:

```sh
python3 verify_all.py
```

This runs each check in its own process, avoiding import-name collisions:

```sh
python3 comparison/verify_comparisons.py
python3 verification/source_zero_jumps/verify_zero_jumps.py
python3 verification/zero_jump_machine/verify.py
python3 verification/jump_products/replay.py
python3 verification/low_level_search/verify.py
python3 experiments/formula_recoding/check_witnesses.py
python3 experiments/base8_parity/build_b8.py
```

`verification_results.json` records the packaged verification run. The
default commands validate source contracts, exact finite witnesses, graph
identities, retained emitter witnesses and saved finite-search evidence.
They do not silently claim to rerun every large search or build Lean.

The complete recursive inventory can also be regenerated against a checkout
of the pinned repository (the original ZIPs are not duplicated in this packet):

```sh
python3 comparison/audit_all_archives.py --repo /path/to/ProveIt --output /path/to/new_inventory
```

For the larger searches, see the individual READMEs. In particular:

```sh
python3 verification/jump_products/replay.py --folds
python3 verification/rejected195_repairs/repair_candidate.py
python3 verification/rejected195_repairs/two_row_dispatch.py
```

The first command requires g++ and takes several minutes. The low-level
packet provides the separate complete search sources and commands for its
38,220 ordered state identifications. All negative conclusions are restricted
to the declared window, stuttering bound and mutation grammar.

## Table conventions and negative controls

Tables use five columns: state, read bit, write bit, `L` or `R`, next state.
The tape alphabet is `{0,1}`, blank is0, and the tape is infinite both ways.
The separate halt label is excluded from the working-state count.

The new 196-state positive table uses start0 and halt196. Rejected sparse
195-state tables omit a working label but can still use halt196. The B8
prototype has working labels numerically greater than196 while halt remains
196; count distinct first-column states, not the largest integer label.
Every machine's README or receipt states its conventions.

Files named `rejected195.tm`, `candidate195_sparse_dense.tm`, and
`wrong_opcode_parent196.tm` are deliberately retained negative controls.
They must not be presented as validated consistency machines. The runtime
failure is an exact source-binding failure, not a proof of every possible
halting property of the wrong table.

## Build the report

With a normal TeX Live or MiKTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses standard packages including amsmath, lmodern, longtable,
microtype, xurl and hyperref. `pdf_quality.json` records the final layout
checks. The PDF was rendered and visually inspected before delivery.

## Contents and provenance

- `comparison/`: full inventory, archive hashes, selected tables and graph
  comparison checker.
- `verification/source_zero_jumps/`: the complete 274,880-pair inductive
  source certificate and source-equivalence theorem.
- `verification/zero_jump_machine/`: exact source/table/startup certificate
  and independent rejection of the new195 candidate.
- `verification/jump_products/`: interacting action synthesis and fold search.
- `verification/low_level_search/`: scanner and whole-state finite-template
  searches with explicit scope and receipts.
- `verification/rejected195_repairs/`: the two focused repair families.
- `experiments/base8_parity/`: 202-state integrated runtime prototype.
- `experiments/formula_recoding/`: tag-swap and disequality emitter witnesses.
- `reference/pa196/`: the pinned upstream PA196 reference development and
  its original license; it was not newly built as a full Lean project here.

Original authorship and licensing are preserved in each component. The table
architecture, baseline logic and most symbolic engine lemmas are inherited
from James Chang and the cited ProveIt/incoming work. New investigations
and adaptations are identified by their READMEs. `MANIFEST.sha256` covers the
delivered files except itself and disposable execution caches.
