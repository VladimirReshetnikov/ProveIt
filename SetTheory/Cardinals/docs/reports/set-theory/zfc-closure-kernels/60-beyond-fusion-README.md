# Runtime synthesis and a rewritten 255-state decoder

This packet accompanies the research report. **It does not contain a machine
with fewer than 252 states.** Its positive runtime artifact is a different
255-state binary Turing machine for the direct arithmetic negation rewrite.
The packet also supplies a complete, independently audited finite search
ledger for a new family of attempted reductions of the existing 252-state
machine.

All scripts use Python's standard library. Python 3.9 or later is required.
Run without `-O`: assertions are verification conditions. No ProveIt checkout,
network connection, Coq installation, or third-party package is required.

## Quick verification

From this directory run:

```sh
python -B verify_coverage.py
python -B phase_followup.py
python -B verify_runtime.py
python -B verify_direct_coverage.py
```

These commands write fresh reports in `evidence/` and print compact results.
The coverage commands usually take about a second each; the symbolic and
literal checks take a few seconds each, depending on hardware.

`verify_coverage.py` reconstructs the attempted reduction family independently
of the search driver. It proves that the recorded ledger contains exactly one
entry for each prescribed recipe, in the specified order, and that the summary
counts and SHA-256 hash match. It **does not replay the recorded symbolic
traces**. `phase_followup.py` does replay all 1,674 recipes whose recorded first
failure was one of the six excluded source guards; all fail on a retained guard.

`verify_runtime.py` checks every one of the 7,311 instruction guard contracts of
the frozen direct-negation DAG against `inputs/direct255.tm`, verifies the 55
protected register-support rows, and then literally simulates the entire
82,552-step blank prefix. It checks equality of the whole finite set of one
positions with the existing 252-state machine's clean root configuration;
every other tape cell is zero. The output includes one record per guard case.

## Meaning and limits of the runtime check

The unchanged `strict_affine.py` is the pinned ProveIt source27 sufficient
checker. It symbolically handles arbitrary affine zero-run lengths and
register values satisfying the case guard. Its four register-box contracts
are assumptions inherited from the attributed upstream verification. The
255-state table preserves the same 55 binary transitions on which those
contracts depend. Each successful instruction also has a positive literal
transition count, so its progress witness is not solely a macro step.

This finite Python audit is conditional on those register-box contracts and
the soundness of the checker rules. It is not a kernel-checked proof. The
arithmetic correctness of the changed negation source, its scratch-register
precondition, and the calibration to `Con(ZFC)` are separate obligations
discussed in the accompanying report. No successful blank prefix alone proves
an infinite computation, consistency equivalence, or independence.

## The synthesized state-fusion family

For a deleted state `q` and retained state `r`, every transition target `q` is
replaced by `r`. A pair is admitted when exactly one of the two binary actions
of `q` and `r` agrees after this quotient. The common action remains fixed;
the conflicting action of `r` is synthesized from every binary write, every
left/right move, and every retained working-state or halt target. The start,
dispatcher, and all 55 protected register-support rows remain fixed. Equivalent
orientations of two eligible states are represented once.

The frozen 252-state table yields 264 admitted pair/bit kernels. Each has 251
retained working states plus the halt target, hence 1,008 possible synthesized
actions. The ledger contains all **266,112 recipes**, with **zero survivors**
of the sufficient checker at fuel 1,000. It records 340,724 candidate case
checks. The three rejection categories are:

| Sufficient-checker outcome | Recipes |
|---|---:|
| Unsupported symbolic transition or invariant | 159,013 |
| Symbolic fuel exhausted | 105,234 |
| Missing transition in the quotient | 1,865 |

An unsupported transition or exhausted fuel does not establish semantic
inequivalence. This is a negative result for an explicitly bounded checker and
family, not a lower bound on Turing-machine size.

The six source guard exclusions are `8202`, `8203`, `8204`, `8358`, `8359`, and
`8360`, using the original depth-first case indexing in `Prog254.v`. Their
unreachability is supplied by the separately established source phase
invariant. Exactly 1,674 recipes had first failed on one of these guards.
Rechecking those recipes with all other 8,385 guards required yields no
survivor. All other recipes already have a recorded rejection on a retained
guard. This follow-up relies on the separate phase invariant; the script does
not prove it.

To reproduce the full search rather than only audit its coverage, run:

```sh
python -B synthesized_fusion.py --seconds 900 --output recomputed-fusion.json
```

Allow several minutes. A time limit produces an explicitly `partial` result;
the included original run has `status: completed`. The synthesized transition
family, frozen inputs, and guard construction are unchanged in the portable
driver. Its path setup was adapted to this directory. The exact original
driver used for the recorded run is retained as `recorded_search_driver.py`
solely for provenance and expects the original checkout layout.

## Final bounded search on the changed 255-state machine

The same compatible-action family was applied to the frozen direct255 table.
It has 275 admitted pair/bit kernels, with 1,020 actions per kernel, for a
complete family of **280,500 recipes**. There are **zero survivors** at affine
fuel 1,500, using all 7,311 changed-source guard contracts. Recorded rejection
counts are 181,353 unsupported outcomes, 97,071 exhausted-fuel outcomes, and
2,076 missing-transition outcomes.

This run has an explicit provenance boundary. An interrupted ledger contained
219,939 complete failed-recipe records and one incomplete final line. The
continuation reconstructed and structurally audited every complete prefix
recipe, retained its exact bytes, excluded the incomplete line, and evaluated
only the **60,561 remaining recipes**, performing **63,827 fresh case checks**.
The continuation did not freshly replay the symbolic failures of the recorded
prefix. The joined ledger is nevertheless complete; its prefix is recorded
earlier evidence and its suffix is the newly executed continuation.

`verify_direct_coverage.py` independently reconstructs all 280,500 recipes,
checks the full joined ledger, and verifies exact preservation of the complete
original prefix. It performs no symbolic-trace replay. The original prefix,
including its deliberately retained incomplete final line, is provided for
reproducibility; it should be read through this verifier or the continuation
driver, not treated as a wholly valid JSONL file.

To reproduce exactly the final continuation, run:

```sh
python -B resume_direct255_prefix.py --seconds 900
```

This uses only bundled inputs, first rechecks all 7,311 baseline contracts,
then audits the recorded prefix and reruns its untested suffix. Output goes to
`direct255-resume-recheck/`; it does not overwrite the included evidence. The
original continuation took about 44 seconds. Timings may vary. A timeout is
reported as `partial`, with all completed records retained.

The same sufficient-checker limits described above apply to this family. A
complete negative ledger does not prove that no valid 254-state, 253-state, or
smaller machine exists.

## Included files

- `inputs/permutation252.tm`: the unchanged pinned original old-label table.
- `inputs/Prog254.v`: the unchanged original 6,460-leaf program used to construct
  the 8,391 original guard cases.
- `inputs/strict_affine.py`: the unchanged sufficient checker.
- `inputs/audit_helper.py`: unmodified constant/function excerpts of the pinned
  independent ProveIt audit, with a standalone import header.
- `inputs/direct_fused_dag.json`: the 203-node, 5,650-leaf arithmetic-negation DAG.
- `inputs/direct255.tm`: the frozen 255-state machine checked against that DAG.
- `evidence/fusion-clean.jsonl`: every full-search recipe and its first recorded
  failure. Row format is `[deleted, retained, changed_bit, write, direction,
  target, failed_case_index, reason]`.
- `evidence/fusion-clean.json`: the complete original search summary and group
  counts; timings and original driver hash are retained.
- `evidence/fusion-clean-coverage.json`: the original independent coverage audit.
- `evidence/fusion-phase-followup.json`: the original 1,674-recipe phase follow-up.
- `evidence/direct255-verification.json`: the fresh portable 7,311-case and exact
  blank-prefix verification, produced by `verify_runtime.py`.
- `evidence/direct255-ledger.jsonl`: the complete final 280,500-recipe ledger.
- `evidence/direct255-search.json`: final search counts, continuation counts,
  recorded-prefix hash, and joined-ledger hash.
- `evidence/direct255-original-prefix.jsonl`: the exact recorded prefix, with
  its one incomplete final line preserved for provenance.
- `evidence/direct255-coverage.json`: independent complete-family and exact
  prefix-preservation audit.
- `sources.json`: attribution, pinned source paths, and input hashes.

The TM files use old integer labels, which need not be consecutive. State `64`
is initial, state `96` is the decoder dispatch state, and label `254` is the
halting state. Label `254` has no binary rows and is not counted as a working
state. New working-state labels may exceed `254`; count the distinct row-source
labels rather than taking the largest label.

The input table hashes are:

```text
permutation252.tm
939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713

direct255.tm
120fb2885194f45b08c8586161683bab103e506d3d3db6f71a3634a024e2ebc8

fusion-clean.jsonl
60e7a44066339e0979cb4ad172c0f0368812fe305fbfa1b928262da40946d690

direct255-ledger.jsonl
3891d8532b0ebe2bd178e14fc94cd09bbffb8da89dc3c4b8b95f47ed41db1f0a
```

The upstream attribution is retained in `sources.json` and the report. The
underlying 254-state machine, 253-state reductions, 252-state permutation, and
the strict checker are prior work. This packet contributes the new synthesis
experiment, its coverage audit, the arithmetic-negation runtime artifacts, and
the standalone reproduction wrappers.
