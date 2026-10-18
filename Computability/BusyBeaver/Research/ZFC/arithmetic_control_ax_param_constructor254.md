# Internal AX parameter push and implication constructor

[ArithmeticControlAXParamConstructor254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXParamConstructor254.lean) composes the actual parameter1 push at **222→248** with the implication constructor at **248→275**. For every internal register file in a model of IΣ₁, with both scratch coordinates initially zero, it supplies a positive internal execution time for **222→275** and the exact output:

```text
TW := wim(oldTW, oldP1)
```

Every other coordinate retains its original value, including the entire WS stack, P1 and both scratch coordinates. The parameter push temporarily writes `cantor(oldTW, oldWS)` to WS and copies P1 into TW. The constructor takes the two Cantor projections, restoring oldWS and combining oldTW with oldP1. The proof uses the checked parent contracts, internal Cantor identities, register-write equalities and addition of internal execution times. It introduces no finite-fuel bound or semantic execution premise.

The [typed audit](arithmetic_control_ax_param_constructor254_audit.lean) has five named axiom probes and seven callers. It covers the control join, complete-file cancellation, changed and preserved coordinates, WS/P1 preservation and the runtime theorem. The first actual source/audit run passed in 3.380 and 1.804 seconds with zero warnings. The control-join theorem has no axioms; the other four reports use only `propext`, `Classical.choice` and `Quot.sound`. The [raw verification record](results/arithmetic-control-ax-param-constructor254-verification.json) preserves the exact commands, logs and fresh-object captures before audit.

The [independent evidence review](results/arithmetic-control-ax-param-constructor254-review.json) checks all 237 recorded inputs, the selected 103-project closure and actual first providers. The cached external boundary consists of five directly imported Foundation/Mathlib modules plus the inherited `Foundation.FirstOrder.Arithmetic.HFS.Seq` pair, with Init and Omega explicit. The reviewer subsequently prepared the publication script; root-owned proof execution, installation and maintained preparation remain separately recorded. The [history](results/arithmetic-control-ax-param-constructor254-history.json) retains the source-only review, its metadata reader, the unbuilt preparation, first actual PASS, raw logs, root receipts and exact source/audit/guard bytes. No failed proof attempt for this module is claimed.

The immediate parents are the exact AXParamPush run2 and AXConstructor run1 PASSES. Each parent and this module record both the source object and its first provider before audit. Their earlier dependency provenance retains its original scope. The [provider proposal](results/arithmetic-control-ax-param-constructor254-provider-proposal.json) pins the historical source/object pairs. Replay requires those exact cached providers; no compiled caches are distributed and no clean-checkout dependency rebuild is certified.

The maintained [guard](check_arithmetic_control_ax_param_constructor254.py) changes only the source, audit and provider-proposal defaults. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_param_constructor254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-param-push254-verification.json \
  --constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-constructor254-verification.json \
  --output /tmp/fresh-ax-param-constructor-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, 4,096 MiB and a shared 120-second budget. This closes the stated AX segment. The full AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
