# Internal AX prefix through the second implication

[ArithmeticControlAXSecondImp254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXSecondImp254.lean) composes the checked [first implication prefix](arithmetic_control_ax_first_imp254.md) with the [parameter push and constructor](arithmetic_control_ax_param_constructor254.md), proving the actual control path **41→275**. For every internal register file in a model of IΣ₁, with S1=S2=0 initially, the theorem supplies a positive internal execution time and the complete output file:

- `TW := wim(wim(oldAC, first(second(oldPL))), oldP1)`;
- `WS := cantor(wal(oldP1, oldCache), cantor(oldTW, oldWS))`;
- `cache := oldCache + first(oldPL)`;
- `PL := second(second(oldPL))`;
- all other five coordinates unchanged, including AC, P1 and both scratch coordinates.

The proof joins the two actual contracts at control 222. The intermediate parameter push and constructor restore WS, so the earlier prefix's WS, cache and PL effects remain exact. All data and clocks are arbitrary internal values; the contract has no fixed fuel or standardness restriction.

The [typed audit](arithmetic_control_ax_second_imp254_audit.lean) contains seven named axiom probes and ten callers, including arbitrary retained coordinates, AC and both scratch coordinates. The first actual run passed in 2.787 seconds for source and 2.015 seconds for audit, with zero warnings. The control join uses no axioms; the six field/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-second-imp254-verification.json) preserves the exact commands, outputs and source object captured before audit.

The [existing-evidence review](results/arithmetic-control-ax-second-imp254-review.json) checks all 257 actual inputs, their preparation counterparts, 113 selected project providers, six cached Foundation/Mathlib pairs (five directly imported), Init/Omega and the fresh first provider. Both immediate parents genuinely recorded their source object and first provider before audit. Older ancestor evidence retains its original scope. The reviewer independently read the root-authored source and audit, authored this unit's strict guard, and subsequently reviewed root's actual execution; these roles are recorded explicitly.

Before freezing or compiling the source, the author corrected the namespace opening for `axEntry` and `cacheReg` to their actual Dispatch namespace. [The history](results/arithmetic-control-ax-second-imp254-history.json) retains that authoring note, the corrected source/audit bytes archived before guard authoring, source review, guard proposal, preparation, first actual PASS, raw logs and root receipts. It does not invent unavailable earlier draft bytes or a failed proof attempt.

The [provider proposal](results/arithmetic-control-ax-second-imp254-provider-proposal.json) retains the exact source/object union selected from the two successful parent records, including historical scratch source paths. Replay requires those exact cached providers. Compiled caches are excluded from publication; a clean-checkout dependency rebuild is not certified. The retained `HFS.Seq` pair is an inherited boundary in addition to the five directly imported external modules.

The maintained [guard](check_arithmetic_control_ax_second_imp254.py) changes only its source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_second_imp254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --first-imp-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-first-imp254-verification.json \
  --param-constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-param-constructor254-verification.json \
  --output /tmp/fresh-ax-second-imp-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit with default proof limits, one thread, 4,096 MiB and a shared 120-second budget. The later AX controls, complete interpreter/Enum correspondence and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
