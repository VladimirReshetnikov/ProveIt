# Offline machine engineering supplement

This package accompanies the exact-hull research report. It includes two
compiler controls, an attributed prior 253-state machine, and a bounded
state-fusion experiment. **It establishes no new machine-state bound for
Con(ZFC)** and no new internally formalized ZFC equivalence.

The source inputs are pinned to ProveIt commit
`de047657e193ec605e930eaf149a44a38031820b`; the 253-state prior machine is pinned
to mira-emmy's commit `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

## Reproduce offline

Use Python 3.11 or newer with its standard library. From this directory:

```sh
python3 reproduce.py --quick
```

No network access, Git checkout, package installation, Coq, or Lean is needed.
The driver reads only supplied files, disables Python bytecode writes, and
uses a temporary directory for regenerated tables and certificates. An optional
`--output /path/to/report.json` saves the verification report.

The quick check:

1. Checks all 21 pinned input-file hashes and sizes.
2. Verifies the exact four-row old-label change, deletion of old state 8,
   and complete label bijection between the baseline and the supplied
   253-state literal machine.
3. Reexecutes all 312,975 literal blank-tape initialization moves and checks
   the complete finite tape, including its 178 one cells.
4. Regenerates both selected compiler controls from their exact formula
   words and winning recipes. Named/literal tables, grammar, state labels,
   source/target DAGs, and operation certificates must be byte-identical.
5. Runs the independent operation-certificate checker and directly checks
   totality, state counts, transition closure, and graph reachability.
6. Checks the complete fusion ledger against its failure census. This
   ledger check does not repeat the full fusion search.

The copied package passed this command from `/tmp`; the executed record is
`quick_verification.json`. It reports:

| Control | Working states | Rows | Related operation pairs | Successor comparisons |
|---|---:|---:|---:|---:|
| `EPSC_s` | 270 | 540 | 3,620 | 5,162 |
| `EFPC_010` | 271 | 542 | 4,028 | 5,744 |

### Optional complete experiments

```sh
python3 reproduce.py --full-search --output /tmp/efpc-full.json
python3 reproduce.py --fusion --output /tmp/fusion-full.json
```

`--full-search` additionally recompiles all 20,480 selected grammar candidates
and compares all ten distributions and winning recipes with the recorded
aggregate. `--fusion` additionally repeats the 148,368-candidate bounded
fusion search and compares the uncompressed candidate ledger. Both options
first perform the quick checks. Their original full experiment results are
included. Packaging verification reran the quick checks and the complete
20,480-candidate grammar search; `full_search_verification.json` records a
successful 66.255-second offline replay with every distribution and recipe
matching. The complete fusion search was not repeated during packaging.
Runtime depends on the computer: the original full grammar experiment took about one minute,
and the original fusion search about three minutes.

## Contents and interpretation

- `fixedpoint/EPSC_s/` reproduces the prior 270-state EPSC control exactly.
- `fixedpoint/EFPC_010/` is the new 271-state EFPC engineering control.
- `fixedpoint/results.json` records all 20,480 compiled candidates in
  per-presentation distributions, including actual framework costs.
- `fixedpoint/literal_audits.json` records independent literal audits of all
  ten original winners. Only the two selected winner directories are packaged.
- `fusion/` includes the experiment result, transition usage, and compressed
  first-failure ledger. Its census is 132,389 fuel exhaustions, 15,336 symbolic
  abstraction limits, and 643 unexpected halts. There were no accepted
  candidates. Timeouts and abstraction limits remain unresolved; this is not
  a semantic no-fusion theorem.
- `baseline/` contains the attributed 253-state literal machine, whole-tape
  bootstrap endpoint, and source/attribution record.
- `vendor/ProveIt/` contains the 20 unchanged source/license files needed
  by these scripts. It is a minimal input subset, not a checkout or a complete
  upstream verification project. Historical upstream READMEs are retained
  verbatim and can refer to files outside this subset.
- `SOURCE_MANIFEST.json` identifies every unchanged supplied input.
- `ENGINEERING_NOTES.md` discusses the results, proof boundaries and route
  to further machine reductions.

The finite operation certificates compare a compressed control with a naive
program emitting the same formula word. They do not prove the new theory's
emitted-code soundness/completeness, binary compiler/initializer simulation, or
an internal arithmetized ZFC theorem. The 253-state machine and its formal
proof lineage are prior work, not a new construction in this report.

## Attribution

Read `ATTRIBUTION.md`. The included original license texts are retained
without extending their grants to unrelated third-party material.
