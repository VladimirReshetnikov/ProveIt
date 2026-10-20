# An arbitrary protected stack tail for the native enumerator

The exact candidate scheduler starting at `np = 0` or `np = 1`, with `pl = 0`, never reads its initial theorem stack. Every NIP pops a formula pushed later. Thus an **arbitrary initial stack** is permitted when the current formula and cache are theorems. The [ordinary proof](proof.md) gives an all-natural Cantor-diagonal induction, followed by the soundness invariant and the inherited arbitrary-cutoff completeness argument.

This can accommodate the relay217 startup's contaminated stack **after** the complete AX suffix returns a bundle axiom and clears the cache. The [exact source-contract connection](source-contracts.md) identifies that state and the retained compiler interface. It does not certify a 217-state machine: the relay has a recorded primitive-runtime failure, and its binary simulation remains a separate obligation. No new Lean or Rocq proof was run.

The [independent peer](peer/review.md) and [root review](peer/root-review.md) both accept the ordinary scheduler argument. The earlier [relay seed review](references/relay-seed-review/analysis.md) correctly rejects applying the usual whole-stack invariant at the dirty intermediate frame; the new proof protects the initial tail instead.

## Exact interfaces and evidence

- [Enum222](../../../Lean/BusyBeaver/ZFC/Enum222.lean) supplies the exact fetch/command schedule and the `Contract`/`build` interface, universally quantified over an arbitrary retained stack.
- [L2Axioms219](../../../Lean/BusyBeaver/ZFC/L2Axioms219.lean) supplies the `l305`/`e305` normal AX suffix contract; [L2Root219](../../../Lean/BusyBeaver/ZFC/L2Root219.lean) supplies arbitrary-state `root_step` and `iter_iff`.
- Source146's [general seed lemma](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/146-r218-res-src218-general_seed_lemma.md) supplies the separate cofinal `START_U` extension. The maintained `Enum222.complete` alone states the original zero-seed theorem.
- The independent [bounded arithmetic check](schedule-check.json) covers 100,001 candidates, 124,710 command instances and all within-candidate prefixes, with minimum conservative balance zero. It checks schedule arithmetic only; the finite census is not the proof of the all-natural theorem.

The checker is self-contained standard-library Python. To reproduce in a **fresh** scratch directory without replacing the saved records, copy `check_schedule.py` there and run `python3 -B check_schedule.py`. It writes `schedule-check.json` beside itself. No supplied simulator, runtime suite, source generator or proof compiler is invoked.

`opening_encoder` authored the theorem, source connection and bounded checker. `review_upstream_reflection` independently checked the full ordinary proof and earlier relay trace scope; root independently checked the proof and retained interfaces. [Publication metadata](publication.json) preserves exact input hashes, copies and these distinct roles.
