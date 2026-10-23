# K215 proof simplification: checked components and a consolidation plan

**Start with [report.pdf](report.pdf).** Its editable source is
[report.tex](report.tex).

This packet proposes how to simplify the existing K215 correctness proofs
without changing the machine, source program, or public consistency statement.
It is prepared for incorporation into Vladimir Reshetnikov's ProveIt repository.

All work is pinned to:

    cbf94cb552a3b49509e0eee80e7455d4eb5974c6

[Pinned repository](https://github.com/VladimirReshetnikov/ProveIt/tree/cbf94cb552a3b49509e0eee80e7455d4eb5974c6)

## Recommended order

1. **Native Replacement and its necessary import split.** Reuse the existing
   quotient Collection theorem, apply a guarded functional-image lemma with native
   equality, and separate generic finite attempts from their legacy specializations.
   The supplied patch is checked through the generic endpoint and compatibility clients.
2. **A common Rocq runtime.** Port the table-parametric register-engine boundary
   already present in Lean. Five runtime proof bodies are repeated across eight
   variants. A checked finite-support transport prototype specifies one reuse
   obligation; the common runtime integration remains future work.
3. **Optional termination transport.** Replace local halting-time subtraction by
   induction over reachable suffixes. The actual KSim patch is checked, but its
   new library has a net source cost until shared by enough clients.

The underlying guarded-image and reachable-suffix ideas occur in earlier
repository proposals. This packet contributes current-source integration,
checked adapters, exact dependency accounting, and reproduction evidence.
It makes no discovery-priority claim.

## Results and accounting

| Change | Completed check | Measured effect |
| --- | --- | --- |
| Native Replacement | Lean 4.32.0; 107 project modules plus two audit clients, all successful | Literal endpoint source closure: 174 to 173 modules, 1,752,650 to 1,744,292 bytes, 37,648 to 37,483 physical lines |
| Native compatibility | All old Replacement APIs and finite-attempt specializations checked | Retaining compatibility adds 3,902 bytes and 84 lines across maintained affected sources |
| Rocq sharing prototype | Coq 8.16.1 compilation and recursive coqchk; six closed reports | 318,724 bytes inventoried in seven additional copies of five runtime modules; no net refactor saving claimed |
| Termination transport | Fresh original runtime build, new library/adapters/counterexamples, actual patched KSim | Client file 354 to 326 lines; client plus new production modules 354 to 542 lines |

These are source/import metrics, not proof-object sizes or comparative build
timings. The two Lean changes were checked separately.

## Verification boundary

The native check includes the generic KEndpoint theorem, the affected semantic
chain, and old APIs. It **does not** rebuild the literal K215 source, boot,
and site certificates under the overlay. The termination check includes the
actual KSim replacement; it does not rebuild the full endpoint. A fresh literal
endpoint build is the final integration gate for either change.

The Rocq prototype uses **Coq 8.16.1 / OCaml 4.13.1**, not the project's production
**Rocq 9.1.0 / rocq-stdlib 9.0.0**. It proves the adaptive query-transport theorem
and a literal 45-row K215/K217 support witness. The representation theorem
connecting that query tree to the maintained executor and the universal Rocq
register-engine port remain to be written. Agreement on the finite support
does not prove equivalence of the whole machines.

The report preserves the repository's distinction between external
proof-assistant equivalence and an internally encoded PA or ZFC derivation.
It provides no new internal consistency endpoint or unconditional nonhalting result.

## Files

| Directory or file | Contents |
| --- | --- |
| [lean-native](lean-native/README.md) | Four production source overrides/additions, repository-relative patch, two audit clients, replay script, dependency census, source-split audit, final successful receipt, raw logs, and exact source snapshots |
| [lean-termination](lean-termination/README.md) | Generic transport theorem, exact K-family adapters, checked counterexamples, actual KSim overlay and patch, replay script, baseline source hashes and compiler evidence |
| [rocq-runtime](rocq-runtime/README.md) | Generic adaptive-query theorem, complete sparse K215/K217 tables and support witness, deterministic producer, duplication census, compiler/checker driver and raw logs |
| [evidence](evidence/) | Baseline and proposed closure censuses, finite explanatory examples, source reviews, and package validation |
| [scripts](scripts/) | Standalone census, finite examples, and bundle verification |
| [NOTICE.md](NOTICE.md), [licenses](licenses/) | Provenance, prior-proposal credit, and retained inherited notices/licenses |
| [MANIFEST.json](MANIFEST.json) | File hashes and byte counts |

No compiler binaries or compiled proof objects are included. Absolute scratch
paths in accepted receipts describe the recorded run; the replay scripts take
new explicit paths. Recorded source snapshots are included for inspection.

## Reproduction

Use Python 3.11+, Lean 4.32.0, and a materialized checkout of the pinned revision.
The Lean component replay uses the official toolchain and project source, with
no Mathlib or prebuilt project cache.

From this directory:

    python3 scripts/verify_bundle.py
    python3 scripts/verify_bundle.py --repo /absolute/path/to/ProveIt

The second command also checks the pinned repository sources. Verification
checks the package and receipt bindings; it does not rerun a proof kernel.

For the native component, use a new output directory:

    python3 lean-native/replay.py \
      --repo /absolute/path/to/ProveIt \
      --lean /absolute/path/to/lean-4.32.0/bin/lean \
      --build /tmp/k215-native-fresh

For termination transport:

    python3 lean-termination/replay.py \
      --repo /absolute/path/to/ProveIt \
      --lean /absolute/path/to/lean-4.32.0/bin/lean \
      --out /tmp/k215-termination-fresh

For Rocq, copy the component first because its checker writes objects, logs and
a new receipt beside its sources:

    cp -R rocq-runtime /tmp/k215-rocq-fresh
    python3 /tmp/k215-rocq-fresh/audit_runtime.py \
      --repo /absolute/path/to/ProveIt
    python3 /tmp/k215-rocq-fresh/check.py \
      --coqc /absolute/path/to/coqc \
      --coqchk /absolute/path/to/coqchk

Use Coq 8.16.1 to reproduce the recorded prototype run. Full integration must
also pass the repository's production Rocq toolchain.

To rerun the source census:

    python3 scripts/census.py \
      --repo /absolute/path/to/ProveIt \
      --out /tmp/k215-baseline-census.json

The optional census overlay argument expects repository-relative paths.
The native component overlay is import-relative; to reproduce the proposed
closure, stage it under a fresh overlay root:

    mkdir -p /tmp/k215-native-overlay/Computability/BusyBeaver/Lean
    cp -R lean-native/overlay/BusyBeaver \
      /tmp/k215-native-overlay/Computability/BusyBeaver/Lean/
    python3 scripts/census.py \
      --repo /absolute/path/to/ProveIt \
      --overlay /tmp/k215-native-overlay \
      --out /tmp/k215-proposed-census.json

## Incorporation

A suitable location for this research packet is:

    Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-native-runtime/

Review and apply the production changes separately from adding the research packet.
From the repository root, the native patch can be checked with:

    git apply --check /absolute/path/to/this-packet/lean-native/native-replacement.patch

That patch contains the new production files as well as the changed imports.
For the optional termination change, copy TerminationTransport.lean and
TerminationTransportK.lean from its import-relative lean directory to the
repository's corresponding BusyBeaver/ZFC directory, then check/apply KSim.patch.
ProgressCounterexamples.lean is an optional audit client.

Rebuild the full literal endpoint, print its assumptions, and preserve the
machine/source hashes before merging production changes. No repository or
remote branch was modified while preparing this packet.

## PDF

    make report

This runs pdflatex until the table of contents and references stabilize.
The source is self-contained apart from standard LaTeX packages named in its
preamble. The report uses immutable source links and includes its bibliography.
The generated auxiliary files are disposable and absent from the archive.
