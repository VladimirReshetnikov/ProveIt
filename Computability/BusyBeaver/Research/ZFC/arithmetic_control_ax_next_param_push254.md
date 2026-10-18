# Internal AX parameter push at controls 275–301

[ArithmeticControlAXNextParamPush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXNextParamPush254.lean) proves the actual parameter1 push at **275→301**. For every internal register file in a model of IΣ₁, with S1=S2=0 initially, it supplies a positive internal execution time and the exact full-file effect:

- `TW := oldP1`;
- `WS := cantor(oldTW, oldWS)`;
- all other seven coordinates unchanged, including P1 and both scratch coordinates.

The copy/restore tail **294→301** has a separate exact-time contract: it takes `7 * oldP1 + 2` internal steps, requires only S1=0, permits arbitrary TW, and changes TW to `oldTW + oldP1` while retaining every other coordinate. The proof instantiates the checked [generic parameter-push contract](arithmetic_control_param_push254.md). Its finite occurrence binds 26 executing instruction edges and 34 successors; the unbounded execution comes from that generic theorem.

The [typed audit](arithmetic_control_ax_next_param_push254_audit.lean) contains six named axiom probes and eight callers, covering the entry/copy/exit bindings, arbitrary retained coordinates, both scratch coordinates, the tail and the full push. The first actual run passed in 63.345 seconds for source and 1.906 seconds for audit, with zero warnings. The three control facts use `propext`; the three file/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-next-param-push254-verification.json) retains exact commands, outputs and fresh-object captures before audit.

The [independent actual-evidence review](results/arithmetic-control-ax-next-param-push254-review.json) checks all 224 recorded inputs, the exact 98-project import closure, six cached Foundation/Mathlib pairs (five directly imported), and Init/Omega. Its separate source review independently decodes all 27 control bindings, including the exit, and the 34 successor paths from the full literal tree. The reviewer subsequently authored the publication builder; root-owned execution, installation and maintained preparation remain separate.

The first uncompiled draft copied the earlier occurrence's exit instruction `decnz 2`. The new exit, control 301, begins an AC push and is `decnz 1`. The theorem and typed caller were corrected, along with the following-block comment, before compilation. [The history](results/arithmetic-control-ax-next-param-push254-history.json) preserves that draft, its correction, the source-only inventory and reviews, preparation, actual source/audit PASS, raw logs and root receipts. No failed proof attempt for this module is claimed. Later continuation plans in that history remain plans.

The [provider proposal](results/arithmetic-control-ax-next-param-push254-provider-proposal.json) pins the generic ParamPush parent and its exact source/object pairs. That older parent recorded its source object before audit but did not save a separate fresh-first-provider field. The guard explicitly resolves its recorded `LEAN_PATH` now; it does not claim that this lookup was captured historically. This new unit records both the source object and its first provider before audit. Replay requires the exact cached providers; compiled caches are excluded, and no clean-checkout dependency rebuild is certified.

The maintained [guard](check_arithmetic_control_ax_next_param_push254.py) changes only its source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_next_param_push254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-param-push254-verification.json \
  --output /tmp/fresh-ax-next-param-push-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, 4,096 MiB and a shared 120-second budget. This contract covers the stated push and its tail. The complete AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
