# PA consistency machines: comparison and reduction study

**Outcome: no valid machine with fewer than 194 working states was established.**

This archive supplies the completed comparison and the reusable results of an attempted reduction. It must not be cited as the construction of a 193-state consistency machine. The exact selector obstruction below applies only to its explicitly specified transformation family; it is not a general lower bound for PA consistency machines.

The target is a binary, single-tape, deterministic blank-start machine `M` with fewer than 194 nonhalting controls and an ordinary proof of

`PA ⊢ (M does not halt on its blank tape ↔ Con(PA))`.

All source comparisons use VladimirReshetnikov/ProveIt commit
`75a42a28ca818627f5a104fb0f0c7f7d02a52947`.

## Start here

- `report/report.pdf` — the complete report, including the 49-class frontier and 61-packet contribution ledger.
- `report/report.tex` and its adjacent `.tex` files — editable report sources.
- `comparison/frontier194.csv` and `comparison/packet_ledger.csv` — machine-readable comparison.
- `inputs/catalogue_index.json` — all 535 retained catalogue representatives, their original paths, table fingerprints, explicit starts where supplied, and byte hashes.
- `verification/helper_obstruction/` — the new exact rational certificate for the frozen primary grammar.
- `verification/factor3/` — the attributed, independently replayed primitive refutation of the already rejected coefficient-three shortcut.
- `verification/check_rotations.py` — the new exact source-reassociation check; its result is deliberately source-only.
- `research/` — search programs, input instances, logs, receipts, and explicit scopes.

## What was established

The fresh audit rechecks 535 retained table classes and distinguishes 49 classes with 194 working states. The historical evidence classification is 33 principal or supported constructions with ordinary PA arguments, five supplementary constructions, six auxiliary tables or seeds, and five rejected tables. These classifications attribute evidence supplied by the original packets; they are not 49 newly reconstructed consistency proofs.

The sole retained 193-state class is explicitly rejected. Its unchanged coefficient-three numerical calculus identifies an equality code with an implication code. A 73,393-step primitive proof derives the designated contradiction, literal one. The certificate uses 116,171 shared arithmetic-expression nodes. Its checker does not admit K/S as oracle rules or use a propositional-tautology oracle.

For the **fixed raw 201-state parent** of primary PA194, an exact rational dual proves that adding any number of fresh direct selectors cannot save more than seven net controls under the specified raw-action, disjoint-reader-fold template. Thus that family has final count at least 194. The verifier reconstructs the finite model from the literal table and checks the dual using exact fractions, without an optimization solver. Newly created action equalities after aliases, helpers targeting helpers, overlapping folds, changed source grammars, and longer detours are outside the theorem.

Two source-tree reassociations preserve all 3,673 resolved primitive instructions and remove the fixed portion's six-consecutive-zero address obstruction. They do not produce a valid shortened-scanner machine: a history-dependent physical reader and blank initialization still need repair.

## Offline verification

Requirements: Python 3.10 or newer, standard library only. No network, solver, repository checkout, Lean, or Rocq is needed for the following command:

```sh
python3 -B verify.py
```

Run from this directory or use an absolute path to the script. Assertions must remain enabled; the check rejects optimized Python. The checks validate the release manifest, catalogue inputs, primitive refutation, exact selector dual, source reassociation, and feasible cost-67 dictionary witness. The last item verifies the witness's word and cost only, not the optimizer's reported lower bound.

The expected overall result is `PASS` with `accepted_sub194_machine: false`. Passing means the stated evidence checks pass. It does not certify a new consistency machine or every historical PA proof.

To build the report on a normal TeX Live installation with pdfLaTeX:

```sh
sh build_report.sh
```

The supplied PDF has already been built and inspected. The core verification command does not need TeX.

## Reproducing the broader work

Each research subdirectory provides its own reproduction notes. The self-contained C++ annealers require a C++17 compiler. The dictionary optimization additionally requires NumPy and SciPy with HiGHS. Some corpus-rescan and exploration scripts require the pinned upstream checkout; those requirements are stated in their local READMEs. Time-limited heuristic searches need not produce exactly the same iteration counts on a different machine.

The corpus audit can be rerun with `comparison/audit_inventory.py`; use its `--help` for argument names. The annotation builder accepts a repository path and an output directory:

```sh
python3 comparison/build_comparison.py /path/to/ProveIt /path/to/comparison-output
```

The fresh scanner recognizes literal numeric five-column tables, complete textual or five-column-array tables in JSON, and distinct nested ZIP payloads. It does not parse every possible transition dictionary or source program. Full original packets remain in the pinned repository; this archive includes their comparison ledgers and retained table representatives rather than duplicating the entire repository.

## Attribution and integrity

See `NOTICE.md`, `licenses/`, and `PROVENANCE.json`. Upstream tables, source programs, and the factor-three certificate retain their original authorship. New material here consists of the cross-packet audit, restricted selector obstruction, source identity checks, supplementary searches, and this report.

`SHA256SUMS` covers every release file except itself. Internal exploratory manifests may document their original subpackage scope. The top-level manifest is authoritative for the assembled archive. All table files are comparison inputs; their presence never implies acceptance as a consistency machine.
