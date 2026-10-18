# Exact 250 pulse and safe initialization

`Prefix250Pulse.lean` proves both three-transition pulse identities on the
exact checked 250-state table, with arbitrary finite left and right contexts.
The `pulse_core` client transfers the identity to the complete infinite tape
through `ZipRep`. The zero/zero case writes 11 and enters old 131; zero/one
restores 01 and enters old 112. Both finish one cell left of the original head.

The generic `PulseSafe` invariant tracks the deposited one just left of the
head in old 255 and the scanned one in old 97. The checked incoming-edge facts
and two literal rows preserve it through every step, including halted
configurations. Induction then proves that every positive-time occurrence of
old 97 in the actual blank run scans one. `initializer_only_at_zero` excludes
any later use of old 97/read-zero. These are unbounded statements about the
actual machine, with no finite-time cutoff or register-value bound.

Root's second guarded attempt passed source and audit, with eight named
axiom probes and five direct callers. Every probe reports exactly `propext`
and `Quot.sound`; no additional axiom or native evaluator is used. Source took
0.796 seconds and audit 0.462 seconds. The one existing source
`unnecessarySimpa` warning is retained; the audit has no warnings.

The first attempt failed during the finite blank-first-step proof at the
default recursion-depth bound, before the audit. The only source repair was
`decide` to `decide +kernel` for that fact. The failed record, complete logs,
and exact source/audit/guard snapshots remain in the history artifact.
The successful source retains its original source-only draft docstring;
verification status is recorded here and in the exact PASS record.

The isolated guard imports four selected project objects: the fresh
`TablePrefix250` and the existing `Core`, `FiniteZipper` and `ZipperRuns`
objects recorded in the MP verification. All 19 input hashes, actual first
providers and the new object before and after audit are recorded. Direct
toolchain boundaries are `Init` and `Lean.Elab.Tactic.Omega`. No dependency
build, download or compiler-version query occurs. Proof commands are serial,
with `-j1 -M4096`, a shared 120-second wall bound and default proof limits.

The maintained guard changes only source/audit default paths. Given the
recorded provider objects, a preparation without proof execution is:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix250_pulse.py \
  --repo "$PWD" \
  --table-evidence Computability/BusyBeaver/Research/ZFC/results/table-prefix250-verification.json \
  --output /tmp/prefix250-pulse-prepared --prepare-only
```

Omit `--prepare-only` and use a new empty output directory for a fresh source
and audit run. The pinned provider records retain their original execution
paths; reproducing their objects is a separate dependency task.

This unit does not yet prove the general register boxes, dispatch simulation,
the 585,431-transition bootstrap, or the blank-tape consistency equivalence.
It asserts no global retiming theorem between different machines and no proof
inside PA. It uses the final table directly, so later concrete box proofs can
use its local identities without introducing an auxiliary machine.

The table and original construction retain the attribution documented in
[candidate-prefix250](candidate-prefix250/README.md): Mira-Cult, Jeff
Ketchersid, Andrew James Wade, mira-emmy and the ProveIt research contributors.
The present Lean proofs extend the repository's whole-tape zipper framework.
