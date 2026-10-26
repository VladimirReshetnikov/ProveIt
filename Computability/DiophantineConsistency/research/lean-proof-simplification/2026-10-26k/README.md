# Further Lean proof simplifications

Prepared 26 October 2026 for Vladimir Reshetnikov.

Repository baseline: `6175dff9a15491497c7a3c1bda4f6a62a6349c74`.
Lean 4.32.0; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

## Start here

Read `report.pdf` (11 pages); its complete source is `report.tex`.
`novelty-audit.md` records 35 earlier ideas deliberately excluded, with pointers
to the current incoming archive and the earlier placed packet.

The six additional ideas are:

1. Reuse `Finset.sum_le_one_iff` for one-hot support classification.
2. Reuse `SignedPellResidue.odd_index_of_base_dvd` for the local Pell parity proof.
3. Derive inverse-pairing graph obligations from a product equivalence.
4. Share the guarded Euclidean certificate across two representation backends.
5. Factor the common affine witness/depth budget of three composition proofs.
6. Use a transitive congruence-up-to-sign relation for Pell sign arguments.

## Patch alternatives

Choose **one** aggregate patch, or review individual patches separately:

| Patch | Contents | Net physical production-line saving |
| --- | --- | ---: |
| `patches/conservative.patch` | Ideas 1–5, including all new helpers/imports | 57 |
| `patches/with-sign-algebra.patch` | Ideas 1–5 plus the sign interface, replacing the native subset | 29 |

Do not apply both aggregate patches. Do not apply `pell-oddness-only.patch`
after the native `combined.patch`; they are alternatives. No GitHub commit,
branch, PR, or push was made by this work.

Both aggregate patches passed `git apply --check` at the pinned baseline.
Their per-file added/removed counts are in `evidence/*-metrics.json`.
The helper-free one-hot and parity changes save 37 lines together. The sign
interface improves proof structure but adds 28 lines relative to that minimal
native subset; its cost is explicitly included above.

## Validation scope

- The **complete modified PairingRepresentation module** compiled, after its
  three baseline dependencies were compiled.
- `projection-and-budget/lean/PairingDataAudit.lean` proves both complete
  inverse-coordinate `GraphRep` values equal to copied baseline definitions
  by `rfl`; their stored expressions and witness counts are unchanged.
- The exact one-hot replacement statement, both general projection lemmas,
  the quadratic/tree obligation shapes, Euclidean helper and uniqueness
  checks, both arithmetic budget regimes, and sign algebra compiled.
- The full current-cell, Pell, quotient/remainder, deeper pairing, and
  GraphSizeBounds modules were **not** rebuilt. The parity-only production
  replacement was inspected and patch-checked, but not kernel-checked as a
  complete theorem in its module.
- New checked files use no `sorry`, `admit`, or extra axiom declarations.
  Axiom probes and compiler output are included. No full repository build or
  performance improvement is claimed.

`evidence/validation-summary.json` is the authoritative compact status table.
Historical execution logs retain their original absolute paths. They describe
the environment used for these checks, not a bundled binary installation.

## Reproduce checks without modifying the checkout

Use an existing ProveIt checkout at the pinned commit, with Lean 4.32.0 and
the project's matching mathlib dependency cache already available:

```sh
python3 scripts/replay.py --project /absolute/path/to/ProveIt
python3 scripts/replay.py --project /absolute/path/to/ProveIt --full-pairing
```

Use `--lake /absolute/path/to/lake` if Lake is not on PATH. Results go to
`replay-results/`, separate from the original evidence. The script obtains
Lake's environment, uses temporary output files, checks the isolated proofs,
and checks both aggregate patches. The second command additionally builds
the three original pairing dependencies, the complete modified pairing
module, and the data-preservation audit. It does not install tools, apply
patches, or run a full project build. The common runner was syntax-reviewed;
the original successful commands are preserved in the per-proposal logs.

For actual adoption, use a disposable worktree at the pin, apply the chosen
patch there, and run the normal affected-module and downstream build. The
remaining full-module checks listed above are real integration work.

## Contents

- `native-proofs/`: one-hot, parity, and optional sign proposals, independent
  patch alternatives, complete candidates, generators, and successful logs.
- `certificates/`: low-dependency Euclidean helper, uniqueness/zero-denominator
  checks, exact wrapper patch, candidates, and metadata.
- `projection-and-budget/`: projection and affine-budget helpers, candidates,
  generators, and the complete pairing data audit.
- `evidence/`: source inventory, source hashes, machine-readable validation,
  production metrics, patch receipts, and successful compiler records.
- `scripts/replay.py`: common isolated replay entry point.
- `SHA256SUMS.txt`: SHA-256 hashes for every delivered file except itself.

## Rebuild the report

The PDF was built with XeLaTeX, Latin Modern fonts, and DejaVu Sans Mono:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error report.tex
```

The `.tex` source and PDF contain the complete report. The report makes a
local novelty claim relative to the inspected prior proposal corpus, not a
claim of novelty in mathematics or the wider Lean literature.
