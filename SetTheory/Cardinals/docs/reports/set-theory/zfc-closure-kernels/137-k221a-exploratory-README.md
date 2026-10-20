# Research seeds only: not certified binary alternatives

The three certified alternatives are in `../machine/`. None of the eleven
seeds in this directory is included in that certification statement.

## Ten literal grammar seeds

`grammar/cost221_0001`, `0004`, `0005`, `0006`, `0010`, `0011`, `0013`,
`0014`, `0017`, and `0018` each contain:

- `candidate.tm`: a literal native-label table with 221 working states.
- `sites.json`: its source tree.
- `allocation.json`: source-to-decoder allocation.
- `compile.json`: discovery-stage decoder checks and explicit missing-proof flags.
- `source_bisimulation.json`: exact source-level comparison with the baseline.

The exact primitive stream and guarded source control flow were checked
unchanged. Source equivalence and decoder allocation are not a complete proof
of the literal binary implementation. Candidate-specific universal binary
runtime and blank-startup obligations remain open. The stored receipts are
research evidence, not main-release verification receipts.

## rho6 source variant

`rho6/` contains a second source family using a bijective parameter renaming
in the sixth axiom schema, with a literal 221-state candidate. Its
`source_schema_certificate.json` records the all-parameter schema comparison
and literal emitter comparison. `compile.json` records decoder checks and
explicitly states that complete runtime and startup proofs are missing.

These artifacts preserve their original internal filenames and historic
discovery paths for provenance. They are not runnable build instructions for
an absent workspace. The self-contained main replay does not need or execute
them. They are included as concrete starting points for the continuing search
for a 220-state construction, not as an additional eleven established results.
