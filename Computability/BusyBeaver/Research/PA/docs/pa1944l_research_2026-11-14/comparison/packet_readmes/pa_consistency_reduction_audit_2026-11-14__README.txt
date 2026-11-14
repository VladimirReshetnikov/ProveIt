# PA consistency machines: comparison and reduction audit

**Result: no verified machine with fewer than 196 working states was obtained.**

This archive is a completed comparison and a reproducible record of further
experiments. It is **not** a claimed solution to the requested strict state
reduction. It contains no new theorem establishing the PA consistency
biconditional for a machine with at most 195 states.

Start with `report/pa_consistency_reduction_report.pdf`. Its editable source is
`report/pa_consistency_reduction_report.tex`, with two included TeX tables.

## Target and conventions

The investigated target is a deterministic binary, single-tape Turing machine,
started on an all-zero two-way infinite tape. All transitions move left or right.
The state count excludes one separate halting control. The requested logical
endpoint is

    PA proves: nonhalting(T, blank) iff Con(PA).

A complete table, a finite startup simulation, a source equivalence, symbolic
instruction checks, an external Lean theorem, and an internal PA theorem are
different forms of evidence. The report identifies which are supplied.

## Main findings

- The source snapshot is ProveIt commit
  `906367250a7f96c923147b10df392294bced7be5`.
- All 27 top-level incoming ZIPs, including their nested ZIPs, were inventoried.
  There are 2,447 recognizable complete numeric binary table occurrences,
  representing 531 byte strings and 522 labeled transition functions. These
  include repeated copies, controls, and rejected experiments.
- The 14 literal 195-state table occurrences comprise eight byte strings and
  six rooted diagnostic constructions. They are not verified solutions.
- The imported PA196 Lean project exposes the internal implication from
  nonhalting to Con(PA). The converse is not supplied by that declaration or by
  the external nonhalting theorem. This limitation is already documented in the
  repository; the audit does not claim the converse is false.
- Four new compositions of the incoming axiom emitters and the MP-success-H
  rewrite have exact transition tables, startup checks, and complete symbolic
  instruction checks. Two use 196 states and two use 197 states. Their new
  arithmetic calibration and internal PA endpoint are not certified here.
- Further parameter, grammar, helper, and bounded scanner searches found no
  reduction. Their negative outcomes apply only to their stated search families.

## Four included experimental constructions

Tables are under `reduction_agent/combination_study/results/`.

| Directory | Working states | Source sites | Symbolic instruction cases |
|---|---:|---:|---:|
| `diagonal_mp_h` | 196 | 3,677 | 4,785 |
| `separate_mp_h` | 196 | 3,650 | 4,750 |
| `diagonal_mp_h_short_neg` | 197 | 3,461 | 4,497 |
| `separate_mp_h_short_neg` | 197 | 3,434 | 4,462 |

Each directory contains a dense table, a native table, a label map, the source
grammar and control graph, chosen contextual folds, and a verification receipt.
Dense tables start at 0 and halt at the label equal to the working-state count.
Native tables start at 74 and halt at 254. Every row has format

    current_state  read_bit  write_bit  L_or_R  next_state

Each machine reaches the same standard clean source seed after 58,154 blank-tape
transitions, with the entire tape and head compared. These finite startup checks
are not nonhalting proofs. The shorter-negation compositions additionally require
an unproved global scratch-zero invariant for their new command calibration.

## Directory map

| Path | Contents |
|---|---|
| `report/` | Final article, compiled PDF, and included TeX tables |
| `comparison_agent/` | All-archive comparison, recursive member/table inventory, corrected 195-state graph groups, new head searches and receipts |
| `comparison_agent/selected_sources/` | Compact frozen incoming compiler, symbolic executor, 101-grammar helper portfolio, reference inputs and licenses |
| `proof_agent/` | Logical audit, exact baseline emitter with admissible variants, dispatcher-return comparison, bounded probe source and receipt |
| `research/` | New source recompression, mixed emitter/association, and finite-window helper searches |
| `reduction_agent/combination_study/` | Self-contained four-machine generator and checkers; 100-grammar composition screen |
| `reduction_agent/scanner_synthesis/` | Restricted Z3 scanner synthesis, exact positive replay and actual solver statuses |
| `reduction_agent/incoming/.../scanner195/` | Explicitly rejected diagnostic inputs retained only for the scanner audit |
| `ProveIt/` | Small pinned source fixture, not a complete checkout or Lean project |
| `evidence/` | Aggregate result, provenance, and final artifact-check receipt |
| `SHA256SUMS` | Checksums for the delivered files |

The `*_agent` names are only directory names retained so that the programs use
their original relative input paths. No external service is needed for the
selected local checks.

## Quick verification

Run from the extracted archive root with Python 3, without `-O` or
`PYTHONOPTIMIZE`. The inherited symbolic executors use assertions.

```sh
sha256sum -c SHA256SUMS
python3 verify_artifacts.py
python3 reduction_agent/combination_study/reproduce.py
python3 reduction_agent/combination_study/scanner_first_return_control.py
python3 reduction_agent/scanner_synthesis/check_positive.py
python3 proof_agent/scanner_source_witness.py
python3 proof_agent/axiom_variants.py
```

`verify_artifacts.py` independently parses both presentations of the four new
machines, checks the counts, state closure, reachability, conjugacy and hashes,
and simulates their complete blank startup frames. `reproduce.py` additionally
regenerates the machines and runs the inherited symbolic instruction checks.
Neither verifier proves the PA consistency endpoint. Reproduction commands may
overwrite their generated receipts; verify `SHA256SUMS` before rerunning them.

The separate scanner controls demonstrate a subtle distinction: an intermediate
return to the dispatcher can have a different tape from the eventual instruction
endpoint even for the correct parent. The two supplied comparisons use different
frames and therefore report different step counts. Both check that the parent
eventually reaches the complete expected frame.

## Repeating the selected searches

These commands rerun the reported families. The exact census needs a complete
checkout, as explained below; the selected search inputs are already included.

```sh
python3 comparison_agent/direct_head_permutations.py --limit 46656 --out comparison_agent/head_permutation_exhaustive
python3 comparison_agent/direct_head_orders.py
PYTHONHASHSEED=0 python3 comparison_agent/anneal_head_variants.py --cycles 40 --steps 2000
PYTHONHASHSEED=0 python3 comparison_agent/anneal_head_variants.py --force-single-head --cycles 12 --steps 6000 --seed 2026111342 --out comparison_agent/forced_head_rotation_search
PYTHONHASHSEED=0 python3 research/grammar_search.py --runs 20000 --seconds 600 --seed 731
PYTHONHASHSEED=0 python3 research/reskin_search.py --seconds 600 --seed 145681
python3 research/extended_helpers.py
python3 research/context_helpers.py --width 2 --out research/context_helpers
python3 research/context_helpers.py --width 3 --out research/context_helpers3
python3 research/context_helpers.py --width 5 --out research/context_helpers5
python3 reduction_agent/combination_study/screen_ties.py
```

The direct parameter family has 93,312 cases and the direct head-order family
has 1,440 cases. The mixed diagonal searches recorded 72,629 and 62,001 applicable
proposals. The original-emitter mixed run recorded 267,965 applicable proposals.
The global pair-recompression run completed 20,000 iterations. Time-budgeted
heuristics can examine a different number of proposals on another computer;
their receipts preserve the actual completed run, not a claim of global
optimality. `research/emitter_search.py` supplies shared functions; its separate
naive compressor experiment was not completed and is not counted as a result.

For optional scanner synthesis, install `z3-solver`. The recorded environment
used Python 3.12.14 and Z3 5.4.1. The positive replay above uses only the standard
library.

```sh
python3 reduction_agent/scanner_synthesis/synthesize.py --states 7 --steps 10 --seconds 30 --readonly --symmetry
python3 reduction_agent/scanner_synthesis/synthesize_mux.py --states 6 --steps 14 --seconds 90 --symmetry
```

The six-counter UNSAT result is restricted to the supplied fixed-entry,
bounded-step, prefix-local template with two additional inherited helper
controls. Longer or less restricted queries returned UNKNOWN. No solver UNSAT
certificate or universal lower bound is supplied.

## Rebuilding the full corpus inventory

The compact `ProveIt/` fixture does not contain the large incoming archives.
Use a separate complete checkout at the exact snapshot:

```sh
git clone https://github.com/VladimirReshetnikov/ProveIt.git /path/to/ProveIt
git -C /path/to/ProveIt checkout 906367250a7f96c923147b10df392294bced7be5
python3 comparison_agent/census.py --repo /path/to/ProveIt
python3 comparison_agent/build_comparison_summary.py
python3 comparison_agent/verify195_groups.py --repo /path/to/ProveIt
```

The last command resolves documented starts for the diagnostic tables and must
follow the summary builder, which otherwise writes the provisional inventory
entries. Recognized literal tables are numeric `.tm`/`.txt` members and repository
`.tm` files; arbitrary JSON/code-embedded tables are outside that particular
count. All 27 main packet manuscripts are nevertheless classified.

## Building the article

Use a normal TeX Live or equivalent installation with pdfLaTeX, latexmk,
Latin Modern, amsmath, amsthm, mathtools, microtype, geometry, booktabs,
longtable, enumitem, xcolor, fancyhdr, xurl, and hyperref:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error pa_consistency_reduction_report.tex
```

The delivered 11-page PDF was compiled and visually inspected. No fresh Lean or
Rocq build is claimed for the new experiments. The exact pinned repository should
be used to inspect or rebuild the original formal developments.

## Attribution and status

See `NOTICE.txt` and `evidence/PROVENANCE.json`. Imported files retain their
licenses, including the PA196 reference attribution to James Chang. No upstream
author is claimed to have reviewed or endorsed these new experiments.

The open deliverable remains an explicit machine with at most 195 working states
and a complete proof of the required consistency equivalence.
