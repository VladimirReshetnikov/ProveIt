# Direct full-seed simplification for the Lean K215 lower bridge

Base revision: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

This packet implements and kernel-checks the previously uncompiled proposal
`verification/k215/simplification/proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md`.
It follows the existing Rocq fresh-code construction in
`k225-formal/rocq224/src/Complete222.v` (`tau_fr`, `th_fr`, `seed_code_fresh`,
and `Q_seed`). The idea is attributed to those repository sources; the new
work is a checked Lean implementation, import pruning, and compatibility checks.

## What changes

`KEind222.c222_complete` asks for a model of the original named formulas, with
literal equality, while its derivability premise interprets their codes using
`th`. This distinction allows the lower proof to establish `FullSeed mem`
directly on the original model. The old route first proved the seed property
only for equality-free matrices and then passed to an indiscernibility quotient.

For a named formula `ψ`, use the matrix `m = ¬¬ψ` and private container name
`k = enc (th m)`. The checked support lemmas give

    Free i f -> i < enc f
    Free i f -> Free i (th f).

Consequently `k` is not free in `m`, and double-negation padding makes `k > 1`,
so the bundle at input/output names `0, 1` is enabled. The named bundle is
derivable because `th` commutes with its membership-only syntax. Its model
semantics gives the seed property for `m`; classical double-negation elimination
then gives the property for `ψ`, including equality atoms.

The endpoint uses the same input domain and the nonempty witness `e 0`.
The tagged-domain construction, its subsequent bisimulation quotient, the
well-founded part, and the ZF/ZFC calibration remain part of the proof.

## Files and compatibility

- `KSeedInterface222.lean` moves the shared named bundle syntax, `DerivableNF`,
  and `KIndisc222.FullSeed` without changing their definitions or public names.
- `KSeedDirect222.lean` proves support, named bundle semantics, `seed_direct`,
  and `fullSeed_direct_of_derivable`.
- `KLowerSeed.lean` imports the shared interface.
- `KEndpoint.lean` uses the direct theorem and the original-domain witness.
- `KSeedModel222.lean` and `KIndisc222.lean` remain optional compatibility
  modules, importing the moved definitions. Their existing proof bodies remain.
- `AuditSeedDirect222.lean` checks the exact generic endpoint type and prints
  nine axiom reports. `AuditSeedLegacy222.lean` checks the old quotient and
  equality-free APIs, with two further reports.

`direct-seed.patch` contains the six production changes. The two audit clients
are supplied in the overlay for replay. The patch passed `git apply --check`
against the stated revision; it has not been applied to the user's remote repo.

## Measured scope

The transitive source closure of `BusyBeaver.ZFC.KEndpoint215` changes as follows:

| Measure | Baseline | Proposal | Change |
| --- | ---: | ---: | ---: |
| Project modules | 178 | 177 | -1 |
| Source bytes | 2,093,112 | 2,086,255 | -6,857 |
| Physical source lines | 40,517 | 40,387 | -130 |

The removed closure members are `KSeedModel222`, `KIndisc222`, and
`Code254Models`; the two new members are the interface and direct proof.
This is a modest source reduction and a more substantial simplification of the
mathematical path. Keeping the legacy API modules makes the repository-wide
source total grow by 184 lines; do not describe the closure reduction as a
repository-wide deletion. No compilation-speedup claim is made.

## Validation result

A final clean replay compiled 112 project modules serially under Lean 4.32.0,
without reusing project objects, in 113.52 seconds on this environment. All
compilations succeeded. The two typed audit clients produced eleven expected
axiom reports and no warnings. Eighteen linter warnings were inherited from
unchanged repository modules; the changed modules and audit clients had none.
Full command, source, import, object, and log hashes are in `evidence/summary.json`
and `evidence/source-manifest.json`. This elapsed time is a replay measurement,
not a baseline comparison or a speedup claim.

## Reproduce

Use an unmodified checkout of the pinned repository and Lean 4.32.0:

```sh
python3 replay_direct_seed.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean \
  --output /absolute/path/to/new-empty-output-directory
```

The script validates the commit, compiler version, and delivered source/import
manifest; compiles serially into a fresh object directory; saves complete module
logs and hashes; checks all eleven audit reports against their expected axiom
sets; and refuses to reuse a nonempty output directory. The source overlay is
read without modifying the checkout. Python 3.11 or later is required.

The replay covers the generic endpoint plus the direct and retained legacy seed
APIs. It does **not** rebuild the machine-specific K215 source certificates,
decoder-site batches, bootstrap, dense table, or the final `KEndpoint215`
module. The latter's source closure is measured, not replayed here. A fresh
full endpoint build remains the integration gate.

The generic ZFC endpoint and the direct seed theorem use exactly
`propext`, `Classical.choice`, and `Quot.sound`. The two support lemmas use
`propext` and `Quot.sound`. No new axiom, `sorry`, `admit`, or native reduction
was introduced. The numerical bundle semantics and its degenerate-role cases
are unchanged, because they are still needed by the upper calibration.

## Attribution

This code is an adaptation of the existing ProveIt development. The named
bundle definitions and `FullSeed` are moved unchanged from the pinned source;
the semantic normalization follows `KSeed222.BundleSemantics`. The fresh-label
strategy is the cited repository proposal and its already-existing Rocq
analogue. Retain the repository's license and existing K215 attribution notices
when integrating these files.
