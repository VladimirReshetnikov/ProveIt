# Internal AX argument push and following plain push

[ArithmeticControlAXArgumentPush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXArgumentPush254.lean) proves three contracts for the actual register program: the argument push at controls **136→162**, the plain push at **162→181**, and their composition **136→181**. Each contract applies to arbitrary internal register values in a model of IΣ₁, assumes both scratch coordinates are zero, and supplies a positive internal execution time.

The first segment pushes the old TW onto WS and copies AC into TW while restoring AC. The second pushes that new TW and clears it. The composition's exact output is `pushFile (argumentPushFile acReg file)`, which means:

- `TW := 0`;
- `WS := cantor(oldAC, cantor(oldTW, oldWS))`;
- every other coordinate retains its old value, including AC and both scratch coordinates.

Finite shape instances bind the actual instruction edges and control successors. The unbounded execution comes from the checked CopyBack and clean-push contracts; the composition adds their internal times. The resolved-target proofs use the existing finite tree-walk helper, program/tree identity, `resolve_source`, and source injectivity. No semantic execution premise is added.

The [typed audit](arithmetic_control_ax_argument_push254_audit.lean) has six named axiom probes and six callers, covering the three control bindings and all three runtime contracts. The first actual source/audit run passed in 57.363 and 1.711 seconds, respectively, with zero warnings. The three control reports use `propext`; the three execution reports use only `propext`, `Classical.choice`, and `Quot.sound`. The [verification record](results/arithmetic-control-ax-argument-push254-verification.json) preserves the exact commands, logs, provider identities and pre-audit object captures.

The [existing-evidence review](results/arithmetic-control-ax-argument-push254-review.json) checks all 225 recorded input paths, the exact 99-module project import closure, six cached Foundation/Mathlib pairs (five directly imported), and Init/Omega. Its author also wrote the guard; that role is disclosed. Separate independent source/API/literal and guard/provider reviews are retained in [the history](results/arithmetic-control-ax-argument-push254-history.json).

Two uncompiled source variants are preserved. The first used an undeclared `c181` alias where the public `exit` control was intended. The second incorrectly renamed the `PushShape` field `pairing` to `plainPairing`; only the assigned private definition should have that name. These two corrections preceded compilation. The selected source passed its first actual attempt; no failed ArgumentPush proof run is claimed.

The sole provider parent is the exact CopyBack run2 PASS. Both CopyBack and this unit record their fresh source object and first provider before the audit. CopyBack's inherited older ParamPush provenance remains explicit. The [provider proposal](results/arithmetic-control-ax-argument-push254-provider-proposal.json) retains exact recorded source/object pairs, including the historical CopyBack source path. Replay requires those cached providers; no compiled caches are distributed and no clean-checkout dependency rebuild is certified.

The maintained [guard](check_arithmetic_control_ax_argument_push254.py) changes only its source, audit and provider-proposal default paths. Preparation invokes no Lean or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_argument_push254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --copy-back-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-copy-back254-verification.json \
  --output /tmp/fresh-ax-argument-push-preparation \
  --prepare-only
```

After reviewing that preparation, omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, a 4,096 MiB memory limit and a shared 120-second budget. This unit does not complete the AX branch, the interpreter/Enum comparison, or the internal binary consistency equivalence.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
