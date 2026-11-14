# U211: a decoder-sharing candidate for Con(PA)

This package gives an explicit **211-working-state, binary, one-tape Turing
machine**, including its blank initializer, with 422 literal transition rows.
It reduces the common supplied U212 construction by nine guarded source
reassociations followed by a predecessor-tag fold. Dense states are 0–210;
state 0 is initial and label 211 is the separate halt. The tape is indexed
by the integers, the head starts at 0, and every cell is initially 0.

Read **report.pdf** for the complete construction, comparison, proof,
verification results, inherited calibration, and complete transition table.
Its editable source is **report.tex**, with sections under **paper/**.

## Proof status

The supplied mathematical calibration and the new source/runtime/startup
arguments give the intended PA-formalizable endpoint

    PA proves: not Halt(U211, blank) <-> Con(U) <-> Con(PA).

This is a conventional mathematical reduction with executable inductive
verification. It is **not** a newly exported Lean, Rocq, MM0, or PA
kernel certificate. It does not assert PA's consistency or unconditional
nonhalting, and it does not claim that 211 states are minimal or that this
candidate is an independently ratified record.

The exact numerical calculus searched by this inherited machine is described
in the report. It is not silently replaced by the separate positive dyadic
proof stream of the unary-theory proposal.

## Reproduce offline

Requirements: Python 3.10+ with its standard library. From this directory:

```sh
python3 reproduce.py
```

This checks the frozen hashes, rebuilds the native and dense tables and source,
independently verifies the nine source rotations, checks the four-case fold
including 12 rejected corruptions, replays the 48,140-step blank startup, and
checks all 5,084 arbitrary-natural primitive contracts. All 422 transition
rows are covered. The full symbolic replay took about 135 seconds in the
preparation environment. No network or search is used.

The complete symbolic engine uses assertions and refuses optimized Python.
Do not set `PYTHONOPTIMIZE` or run the full replay with `-O`.

```sh
python3 reproduce.py --quick
```

The quick command explicitly skips the unbounded runtime replay; it is not a
substitute for full verification. The local fold checker is separately tested
under `-O` because its checks are explicit.

To regenerate the report, also install `pdflatex` and normal TeX packages:

```sh
python3 reproduce.py --quick --pdf
```

`SHA256SUMS` covers frozen inputs, code, machine tables, paper sources, and
retained reference archives. It excludes the generated PDF and evidence files,
which rebuilding regenerates (including variable timestamps and wall time).
Regenerating the PDF may change its hash due to metadata or TeX versions. Each check records and/or
verifies the exact machine inputs it uses. Hashes are checked before any rewrite.

## What is new

All seven complete supplied U212 packets contain the same literal table. The
damaged eighth packet has recoverable builder/receipts for that same result.
The new construction retains that common U212 reduction, including helper 211.

A closed 936-primitive source region at native 174 is reassociated by the nine
rotations in `inputs/rotations.json`. The final source still has 3,909 primitives,
197 distinct subtrees, maximum depth 42, and maximum zero run six. Two physical
selectors become shareable because their unique incoming transitions leave
different bits one cell left of the head. Existing helper 129 consults that
bit. Native state 181 can then be deleted in favor of 220.

The final local fold has an all-common-initial-tapes simulation from state 0:
one old step becomes one or three new steps. The preceding source rotations
change addresses and have a different simulation relation. The whole reduction
uses identical ordinal source control flow, the final canonical runtime, and
the exact common blank startup. Do not apply the local time bound or all-tape
claim across the address-changing rotations.

## Validation results

| Obligation | Result |
|---|---:|
| Working states / transition rows | 211 / 422 |
| Source occurrences / distinct subtrees | 3,909 / 197 |
| Guarded rotations | 9 |
| Internal prefix bindings per audited stage | 3,908 |
| Universal primitive cases | 5,084 |
| Symbolic inference applications | 1,280,108 |
| Literal row coverage | 422 of 422 |
| Minimum duration constant | 5 |
| Exact blank startup | 48,140 steps |
| Startup nonzero cells, with zero exterior checked | 120 |
| Rejected local-certificate corruptions | 12 |

These symbolic contracts quantify over arbitrary natural primary registers,
an arbitrary natural extra header gap, and an arbitrary nonempty finite list
of spare registers. They are not bounded simulations of small register values.
The rules use unary and finite-list induction; they remain ordinary
mathematical proof obligations rather than proof-assistant kernel results.

## Artifacts

- `machine/u211.tm`: dense table, complete and ready for a compatible simulator.
- `machine/u211.native.tm`: same machine in inherited native labels.
- `machine/rotated212.native.tm`: the intermediate for the local fold theorem.
- `machine/sites.json`: all 3,909 final source occurrences.
- `machine/state_map.json`: exact native/dense isomorphism.
- `inputs/`: frozen U212 inputs and rotation recipe.
- `code/`: builder, independently authored source/startup auditors, local
  certificate, inherited symbolic engine, and portable wrapper.
- `evidence/`: full results, per-case certificates, comparison and audit notes.
- `reference/`: complete compact baseline/calibration ZIP, unary-theory ZIP,
  retained license notices.
- `inputs/source_manifest.json` and `evidence/input_comparison.json`: pinned
  source identities and exact original download URLs.

The new replay verifies the U212-to-U211 machine obligations. It does not claim
to replay every inherited logical theorem in a proof-assistant kernel.

## Exact table identity

Native U211 SHA-256:

```text
7edae566b4c2e5c34d88030e0ae7caa49edda32c174b06b1a68bf9eb78567c8d
```

Dense U211 SHA-256:

```text
a529d2ea12b0f4c4185d2fe8ce9dd0f1633c04f39f6bf272bb37bf97bb31a349
```

Source snapshot: ProveIt commit
`9d50bf3df8c9e14941b549945c4f8400172d81f4`, `docs/incoming`.

See `NOTICE.md` for provenance and retained license information.
