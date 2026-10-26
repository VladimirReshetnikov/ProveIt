# Shorter Lean proofs for DiophantineConsistency

Source review prepared 26 October 2026 for Vladimir Reshetnikov.

- ProveIt commit: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`
- Lean: `leanprover/lean4:v4.32.0`
- mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`

Start with **report.pdf**. The complete LaTeX source is **report.tex**, with its
small included `validation-table.tex`. Build it with XeLaTeX twice; required
fonts are Nimbus Roman, Nimbus Sans, and DejaVu Sans Mono. Standard TeX packages
used by the source include fontspec, fvextra, hyperref, xurl and microtype.

## What is included

- `lean/`: independently checked demonstrations, each in a separate namespace
  or file; `validation/validation.json` is the authoritative per-file status.
- `proposals/`: further Lean demonstrations or candidate source modules whose
  integration has not been checked. These are explicitly proposals.
- `patches/`: reviewable patches against the pinned commit. Their validation
  levels differ; read the status file before applying any patch.
- `checked-modules/`: the four complete modified source files used in successful
  PR-congruence and assignment-transport compilation checks.
- `generated-candidate/`: full alternative generated circuit Steps files.
  Static checks preserve all 1,192 public signatures and validate exponent
  labels against literal nodes. Full Lean integration has not been performed.
- `scripts/`: source census, non-mutating candidate generator, independent
  static auditor, and a proof-demo replay command.
- `data/`: per-file hashes, source census, declaration locations, candidate
  metrics, and static audit receipts.
- `validation/`: successful compilation logs, complete modified PR-module
  checks, and an explicit statement of incomplete integration checks.
- `source_notes/`: detailed family-specific source reviews.

The largest generated candidate saves **1,650 physical lines** (6,567 to
4,917), including new helpers and label data. This is a source reduction, not
a measured runtime improvement or a completed repository refactor. The
primitive-recursion patch saves **34 lines** and has been checked in complete
modified files. The assignment-transport patch saves **25 lines** and its
complete modified file also compiled. Ten standalone demonstration files passed.
All mathematical premises and executable program values of those proof-only
replacements are retained. Their exact standard-axiom footprint can change,
as documented below and in the validation record.

## Replay the checked examples

Use an isolated checkout of ProveIt at the exact commit above with its pinned
Lean/mathlib installation. From this unpacked directory:

```sh
python3 scripts/replay.py /path/to/ProveIt
```

With dependencies already built, add `--without-build`. The script builds
only the local imports needed by selected demos, compiles each file separately,
and saves logs and exit codes. It does not apply patches. The default selection
contains only demos marked compiled in the supplied validation record. Use
`--include-proposals` deliberately to experiment with the other demos.

The axiom-marker check is an additional output check, not a complete parser of
Lean environments. Inspect the included `#print axioms` output. Standard axiom
footprints can differ between two valid proofs; the source notes discuss the
recursor-congruence tradeoff and its induction-based alternative.

## Static source and candidate checks

```sh
python3 scripts/inventory.py /path/to/ProveIt census-output
python3 scripts/generate_steps_candidate.py /path/to/ProveIt candidate-output
python3 scripts/audit_steps_candidate.py /path/to/ProveIt candidate-output static-audit.json
git -C /path/to/ProveIt apply --check /absolute/path/to/patches/pr-congruence.patch
```

For the census, a full checkout reproduces the 165 additional archived/provenance
Lean files outside the maintained `Lean` tree. A sparse checkout may omit those
extra copies while reproducing the maintained-tree measurements.

The generated-source patch requires a corresponding update to the upstream
`tools/generate_split_recipe_steps59.py` template and gap wrapper before
integration. The supplied standalone generator proposes the output; it does
not replace the full upstream generation pipeline. Without updating that
pipeline, upstream regeneration checks would overwrite or reject the changed
output. Rebuild Registers/Recipe/Translation clients after adopting it.

The conditional-padding patch changes the theorem API and must be applied to
both its producer and caller together. Other proof-only patches can be reviewed
independently. The source-only alternatives and checked demos sometimes show
different stages of the same interface; do not import alternative declarations
with the same names into one Lean environment.

## Scope and limitations

This packet proposes proof simplifications. It contains no new consistency
decision, no new Diophantine equation, no global optimality claim, and no
completed internal-ZFC equivalence. Selected examples and modified modules were
checked; the entire 546-file maintained tree was not rebuilt. Static signature
checks do not replace Lean elaboration. Runtime improvements were not measured.
No remote repository changes were made.

`MANIFEST.sha256` gives a SHA-256 hash for every packaged file other than itself.
Repository-derived snippets and candidate files are covered by the supplied
MIT No Attribution license. New code in this packet is offered under the same
license.
