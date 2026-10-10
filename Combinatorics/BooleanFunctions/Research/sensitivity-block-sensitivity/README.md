# Sensitivity versus block sensitivity

Research report on total Boolean functions with block sensitivity
superquadratic in ordinary sensitivity, refining openai/math family 132 ("A
superquadratic separation between sensitivity and block sensitivity").
Two AI-assisted, unrefereed manuscripts; nothing is formalized. The
report's article/README write is still pending; this README is a short file
list with a dated reconciliation note. Delivered files are not edited.

## Sources and files

**Part I, *An explicit exponent above 65/32*: the base** (placed
`5476940edc`; unprefixed). `bs(F_m, 0) ≥ (100·2^646)^m` against
`s(F_m) ≤ (9·2^318)^m`, so `bs ≥ s^α` with `α = 2.0320827244… > 65/32`.

- `article.tex`, `verify.py`, `certificate.json`, `BUILD_ENVIRONMENT.json`

**Part II, *Threshold-Resolved Amplification for Boolean Sensitivity***
(placed `18abb81b20`, from `sensitivity_2027_research.zip`; prefix
`02-threshold-`; its TeX is not staged, retrievable from `2c7f4fd68`)

- `02-threshold-FORMALIZATION_PLAN.md`,
  `02-threshold-NOVELTY_AND_ATTRIBUTION.md`, `02-threshold-VERIFICATION.md`
- `code/02-threshold-Makefile`, `code/02-threshold-build.sh`,
  `code/02-threshold-compact_certificate.py`, `code/02-threshold-labels.py`,
  `code/02-threshold-make_tables.py`, `code/02-threshold-profiles.py`,
  `code/02-threshold-test_local_geometry.py`,
  `code/02-threshold-verify_certificate.py`
- `data/02-threshold-SHA256SUMS`, `data/02-threshold-ablation.csv`,
  `data/02-threshold-ablation_table.tex`,
  `data/02-threshold-all_profiles.json`, `data/02-threshold-certificate.json`,
  `data/02-threshold-certificate_run.txt`,
  `data/02-threshold-compact_certificate_run.txt`,
  `data/02-threshold-generated_constants.tex`,
  `data/02-threshold-layers_table.tex`, `data/02-threshold-local_checks.json`,
  `data/02-threshold-local_checks_run.txt`, `data/02-threshold-pdf_qa.json`,
  `data/02-threshold-profile_summary.csv`,
  `data/02-threshold-reproducibility.json`,
  `data/02-threshold-requirements-test.txt`,
  `data/02-threshold-small_label_witness.json`,
  `data/02-threshold-source_parameter_scan.json`,
  `data/02-threshold-source_provenance.json`

Part II's scripts import `profiles` and `labels` by their delivered names
and write `certificates/` and `results/` beside `code/`; rerun them on
copies in a scratch directory under the delivered names, never in the
report.

## Dated note

**2026-10-09, Part II's exponent trails Part I's.** Part II proves
`bs(F_m, 0)/s(F_m)^γ → ∞` for `γ = 3667/1809 ≈ 2.0270868` (seed ratio
`log β/log A ≈ 2.0271708`). Both trail Part I's placed
`α = 2.0320827244 > 65/32`, which Part II does not cite: it compares itself
only with the source release's figures (2.00025, 2.00647). Part II
supersedes nothing in Part I.

Its value is the method and one exact fact:

- Its threshold- and pair-resolved profiles, with a packing lemma coupling
  target and gate candidates (two gate candidates leave at most `t − 2`
  targets, three at most `t − 4`), implement Part I's **open item 3**
  ("Use pair-specific joint profiles") as valid, proved inequalities. Part II
  does not combine them with Part I's level-dependent outdegrees, so
  whether they improve the exponent "after optimization" is still open.
- It **partly answers open item 2** (accuracy of the envelopes): one proved
  target/gate incompatibility, and actual profile maxima against the bounds
  at toy size only.
- It **partly answers open item 4** (label search): a deterministic
  conditional-expectation labelling procedure, without a size reduction.
- New: `bs(F_m, 0) = β^m` **exactly**, through the minimum accepting
  weight. The intake judged that this equality very likely transfers to
  Part I's construction; that is to be checked at the write.
- Part II's own Q2 (level-dependent architecture parameters) is what Part I
  already does.

**Open**: whether Part II's pair-resolved refinements, run on Part I's
level-dependent schedule, beat `2.0321`.

These are the intake dossier's (dossier138_COMB) findings and the placement
message's; they are not re-proved in this note.
