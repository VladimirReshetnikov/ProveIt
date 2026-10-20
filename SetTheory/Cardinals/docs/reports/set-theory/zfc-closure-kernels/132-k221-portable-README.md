# Portable 221-state construction and replay

Python 3.10 or later, standard library only. Run with assertions enabled:

    python -B reproduce.py --output-dir /absolute/path/to/new-empty-output

The default freshly proves all final-machine runtime cases. `--quick` instead audits the stored final runtime receipt. `--full-baseline` additionally freshly replays the 222-state parent and its inherited runtime chain. Outputs must be outside this immutable portable directory. No network access, optimizer, compiler installation, proof-assistant installation, or search trace is needed.

## Deterministic construction

The vendored complete K222 delivery is pinned by SHA-256:
`4f677d8253846069a77dcac648a0a2bfe002ec8530886924ae3eba71e97e00d7`.
Its source construction and numerical-calculus certificates are replayed first.

`build221.py` applies three explicit closed source rotations to that parent's exact source, paired with the corresponding literal decoder rotations. It checks the complete primitive sequence and two independently implemented guarded control-flow resolvers after every rotation. It then folds native state 192 into 172, using state 112 on read 0 and the common direct transition on read 1. The final source has 4,744 primitive occurrences, 185 distinct interior nodes and 13 shared decoder roles. Accounting is 49 + 185 - 13 = 221 working states, plus a separate halt state.

Native table SHA-256:
`e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc`.
Canonical table SHA-256:
`6457dce8c91c5975fb405607567158ca92ad97331f2724503edc0d4ff74cab3c`.
Source SHA-256:
`691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9`.

## Independent obligations

- Exact source-program equivalence to the calibrated parent, including both decrement guards, entry and halt behavior, with negative controls.
- Exact source/allocation identity and every compound decoder edge at every concrete source prefix, with full prefix tape restoration.
- Two separately implemented positive-block fold checkers. They validate the inductive tape facts and all 444 predecessor rows. These are universal all-initial-tape simulations, not bounded blank-tape tests.
- Canonical renumbering and complete blank startup after 409,835 steps.
- Fresh unbounded runtime proofs for all 6,167 guarded primitive cases, with independent arbitrary natural registers, arbitrary extra gap and arbitrary nonempty finite spare lists.
- Independent runtime-receipt and source-invariant audits.

The final runtime and source-invariant receipts are stored under `runtime/reference_results` after their successful execution by the exact packaged driver. Discovery-time receipts are not substituted for these outputs.

The logical calibration is unchanged: source-program equivalence transports the parent's ordinary mathematical consistency comparison. No newly compiled Rocq/Lean theorem for this 221-state table, PA-internal proof, unconditional non-halting, or minimality is claimed. Runtime receipts alone do not establish the consistency comparison.
