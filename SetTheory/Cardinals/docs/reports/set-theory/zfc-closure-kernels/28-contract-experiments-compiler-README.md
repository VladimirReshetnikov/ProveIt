# Bounded full-logic compiler experiments

This directory is a self-contained, standard-library Python reproduction
subset for two completed experiments. It does not contain whole earlier
research archives. Run commands from this directory with Python 3.10 or later.

## Result and scope

The systematic grid evaluated **147,456 DAG recipes**: 12 safe rho8 parameter
permutations, 2,048 seeds, exponents 2/4/8, and legacy/overlap-safe RePair,
with the previously best source19 C/G layout fixed. It reproduced the prior
**268-working-state** table and found no smaller result. The exact cost was
206 decision nodes + 55 framework states + dispatcher depth 7. Across the
grid, dispatcher depths ranged from 6 to 11. Twenty recipes attained 268.
Only the baseline and final winner were compiled; all improving candidates
would have been compiled. The case count is a count of evaluated recipes,
not of distinct programs or compiled transition tables.

The recorded rotation run evaluated **201,600 directed candidates** in 1,400
rounds with seed 2631 and found no smaller result. An earlier 120-round
exploratory run evaluated another 17,280 candidates and also found no
improvement; its redundant outputs are not included. The rotation search
was a stochastic local walk on closed grammar subroutines, not exhaustive.

Both delivered outputs have independently checked 4,533-pair register
control certificates. These establish the stated register-level comparison,
not arbitrary-run binary simulation or nonhalting iff Con(ZFC). The 268
winner is a known compiler control, not a new record. The audit at
`audit_notes.md` gives the repository context and immutable citations.

## Quick winner replay

```sh
python rho8_grid.py --output replay --seeds 1 --start-seed 341 --exponents 4 --modes legacy --perms 0
python vendor/source19/verify_schema_rm_certificate.py --prior-machine-dir vendor/prior --reference replay/reference.dag.json --candidate replay/candidate.dag.json --certificate replay/rm_certificate.json --output replay/independent_verification.json
```

The expected SHA256 of `replay/candidate.tm` is
`77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d`.
The machine has start state 0, working states 0 through 267, and terminal
state 268. Undefined transitions are normalized to a final right move into
the terminal state; the output contains all 536 working-state/read-symbol
rows. The read-1 row of named state `1.inc` is the unique filled halt row.

The packaged quick replay was executed successfully. All eight program
artifacts recorded in `provenance/packaging_verification.json` matched the
delivered full-grid winner byte-for-byte. Runtime metadata and driver hashes
naturally differ between the original and the path-adapted execution.

## Full recorded experiments

```sh
python rho8_grid.py --output rerun-grid --seeds 2048 --start-seed 0 --exponents 2 4 8 --modes legacy safe
python rotate_closed_dag.py --source results/rho8_grid_results/candidate.dag.json --output rerun-rotation --rounds 1400 --seed 2631
```

The original grid took 344.468 seconds and the extended rotation run took
208.824 seconds on the research container. These elapsed times are not
performance guarantees. The packaged full grid was not rerun after the
input path adaptation; the quick replay checks that packaging preserves the
selected winner. The original executed source files remain in `provenance/`.

To independently check the delivered certificates without repeating search:

```sh
python vendor/source19/verify_schema_rm_certificate.py --prior-machine-dir vendor/prior --reference results/rho8_grid_results/reference.dag.json --candidate results/rho8_grid_results/candidate.dag.json --certificate results/rho8_grid_results/rm_certificate.json
python vendor/source19/verify_schema_rm_certificate.py --prior-machine-dir vendor/prior --reference results/rho8_grid_results/candidate.dag.json --candidate results/rotation_extended/candidate.dag.json --certificate results/rotation_extended/rm_certificate.json
```

Each verifier should accept 2,601 INC pairs, 1,931 DEC pairs, and one HALT
pair. Both exits of every DEC pair are checked. The first reference has 217
nodes and the candidate 206; the rotation comparison is 206 to 206.

## Provenance and retained licensing

The audit snapshot is ProveIt commit
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`. The source19 archive arrived at
`be9e617d28ce0032213c27b59c3039c0495e6b83`; its borrowed Jeff/Wade inputs are
pinned to `297ab8df7e5de329605c3875b4934643b371a5e3`.
`provenance/packaging.json` records file hashes and source paths.

All borrowed source files were copied without edits. The two top-level
drivers have only their local input paths adapted; exact executed versions
are retained under `provenance/`. The original source19/prior notices may
describe files from their larger original archives that are absent here.

ProveIt helper licensing is retained in `vendor/proveit/LICENSE`. Andrew
James Wade's compiler licensing is retained in
`vendor/upstream/ZF/generator/LICENSE.wade`. The original calculus/machine is
attributed to Mira-Cult, with Jeff's published formalization and numeric DAG
as identified in the retained notices. This package does not assert a
blanket MIT-0 license over Jeff's specification/DAG or other research files
for which no such grant was supplied; the original notices and provenance
are retained without relicensing those files.

`SHA256SUMS` covers every packaged file except itself. No external Python
package or network access is needed for the replay and verifier commands.
