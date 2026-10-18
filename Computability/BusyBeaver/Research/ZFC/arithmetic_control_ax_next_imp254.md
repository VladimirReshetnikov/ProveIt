# Internal AX implication after a parameter push

[ArithmeticControlAXNextImp254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXNextImp254.lean) proves the actual register-control segment **275→354** by composing the checked [P1 push](arithmetic_control_ax_next_param_push254.md), [AC push](arithmetic_control_ax_ac_push254.md) and [implication constructor](arithmetic_control_ax_ac_constructor254.md). For every internal register file in a model of IΣ₁, with S1=S2=0 initially, it supplies a positive internal execution time and the complete output file:

- `TW := wim(oldP1, oldAC)`;
- `WS := cantor(oldTW, oldWS)`;
- all other seven coordinates unchanged, including P1, AC, cache, PL and both scratch coordinates.

The intermediate AC push and constructor restore WS. The separate **301→354** subcomposition changes only TW, setting it to `wim(oldTW, oldAC)`. Both contracts allow arbitrary internal values and clocks; they impose no fixed fuel or standardness restriction.

The [typed audit](arithmetic_control_ax_next_imp254_audit.lean) contains nine named axiom probes and eleven callers, including arbitrary retained coordinates, both scratch coordinates and expanded whole-file endpoints. The first actual source/audit run passed in 3.531 and 2.161 seconds respectively, with zero warnings. The two control joins use no axioms; the seven field/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-next-imp254-verification.json) preserves the exact commands, outputs and source object captured before audit.

The [independent existing-evidence review](results/arithmetic-control-ax-next-imp254-review.json) checks all 245 actual inputs, preparation inputs, 105 selected project providers, six cached Foundation/Mathlib pairs, Init/Omega and the fresh first provider. Five external modules are directly imported; `HFS.Seq` is a retained inherited boundary. All three immediate parents recorded their source object and first provider before audit. Earlier legacy ParamPush evidence keeps its original missing-capture limitation; unused alternative objects remain provenance only. This reviewer did not author the Lean source or execution guard and did not run the compiler.

[The history](results/arithmetic-control-ax-next-imp254-history.json) preserves the source inventory and original unbuilt freeze, source/guard reviews, provider proposal, preparation, the first actual PASS, raw logs, reviewer sources and root receipts. There was no failed NextImp proof attempt or source repair. Historical status labels remain unchanged.

The [provider proposal](results/arithmetic-control-ax-next-imp254-provider-proposal.json) records the exact source/object union selected from the three successful parent records, including historical scratch source paths. Replay requires those exact cached providers. Compiled caches are excluded from publication; a clean-checkout dependency rebuild is not certified.

The maintained [guard](check_arithmetic_control_ax_next_imp254.py) changes only its source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_next_imp254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --next-param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-next-param-push254-verification.json \
  --ac-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-ac-push254-verification.json \
  --ac-constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-ac-constructor254-verification.json \
  --output /tmp/fresh-ax-next-imp-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit with default proof limits, one thread, 4,096 MiB and a shared 120-second budget. Later AX controls, complete interpreter/Enum correspondence and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
