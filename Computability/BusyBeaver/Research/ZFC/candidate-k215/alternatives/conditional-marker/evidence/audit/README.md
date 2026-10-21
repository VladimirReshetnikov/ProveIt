# Independent audits and scratch-return correction

This directory contains three portable, dependency-free Python 3 audits.
The main `marker215` candidate directory is supplied separately by the main
research bundle. All other required input files are included here.
Run the commands below with this directory as the working directory.

## Marker candidate: independent saved-evidence and blank-tape audit

```sh
python3 audit_marker_evidence.py \
  --candidate /path/to/marker215 \
  --baseline baseline \
  --mapping baseline/legacy_mapping.json \
  --output marker215_independent_evidence.json
```

The candidate directory must contain `marker215.native.tm`, `marker215.tm`,
`sites.json`, `canonicalization.json`, `runtime/runtime.json`, and the
runtime case and startup files. The last two can be either
`runtime/runtime_cases.json` and `runtime/startup.json`, or their `.gz`
versions.

This audit binds the literal native table and source to fixed hashes;
checks every row of the native-to-dense mapping; checks all 6,176 ordered
source guard cases, affine-duration signs, and all 430 covered transition
rows; compares every case with the inherited parent inventory; and
independently executes all 95,714 recorded blank-tape transitions in native
and dense form. It parses the complete resulting finite tape, including
the blank exterior and all 40 spare blocks.

The exact parent-to-variant duration-constant changes are 5,632 cases with
no change, 128 with two extra steps, and 416 with six extra steps. All
variable duration coefficients and net motions are unchanged. The
independent run passes. This script audits the saved quantified evidence;
it is **not** a second implementation of the universal induction checker.

## Comparison with incoming tables

```sh
python3 compare_tables.py \
  --candidate /path/to/marker215/marker215.native.tm \
  --roots novelty_tables \
  --output marker215_comparison.json
```

The 77 files in `novelty_tables` are byte-exact copies selected from the
12 incoming archives and the pinned accepted K215 directory. They are
named by SHA-256; `manifest.json` records their original paths. These are
77 distinct literal 430-row tables, including different state numberings.
The script tests rooted deterministic graph isomorphism with write/read
labels and directions, both directly and with global tape reflection.
It rejects equivalence with all 77, recording a finite conflict witness
for each comparison. This is a precisely scoped novelty check, not a
claim to exhaust all possible prior machines or prove semantic difference.

## Rejecting the archived scratch-biased calibration

```sh
python3 check_scratch_return.py \
  --packet scratch_return_packet \
  --output scratch_return_rejection.json
```

The script independently resolves the structured source control-flow
graph. In the archived candidate, `CC3` at address `100111` returns to
source ordinal 23, not the scheduler at ordinal 0. It checks a literal
15-step source suffix to CH, 72 corroborations of the general `2*T+15`
suffix formula, exact AX-source equality with the parent, and the entire
69,744-step archived blank prefix. It also checks that changing the leaf
to `CC4` restores target 0 but increases the distinct-subtree count from
201 to 203.

The accompanying `scratch_return_correction.tex` gives the all-natural
suffix argument and the precise dependency on the inherited AX
termination and binary simulation theorems. The proof of eventual blank
halting is **not** presented as an executed full halting trace. The
separately executed objects are the finite blank prefix and source suffix.

`adjacent_success_theorem.tex` contains a new cofinality lemma for a
*future correctly implemented* stateful scheduler. It constructs
cofinally many adjacent candidate numbers which both halt under a
refutation; a counter increasing by one or two must meet such a pair.
This source-level theorem does not certify the erroneous archived table.

## Provenance and proof scope

The repository snapshot is
`75716498437bfc7291d5900cab2983a11fd54bac`.
All copied input files and scripts are listed with SHA-256 hashes in
`manifest.json`. The three JSON reports are fresh outputs of the commands
above using the separately supplied marker215 directory. Absolute paths
in reports identify the original run and can differ when reproduced.
The two TeX files are includable sections, intended for the main report;
they use the standard `\path` command provided by `url` or `hyperref`.
