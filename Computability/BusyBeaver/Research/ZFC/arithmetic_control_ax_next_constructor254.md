# Internal AX implication constructor at controls 406–433

[ArithmeticControlAXNextConstructor254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXNextConstructor254.lean) proves the actual **406→433** implication-constructor contract for every internal register file in a model of IΣ₁. With both scratch coordinates initially zero, it supplies a positive internal execution time and the complete output file:

- `TW := wim(first(oldWS), oldTW)`;
- `WS := second(oldWS)`;
- every other coordinate unchanged, including both scratch coordinates.

The occurrence instantiates the checked [generic constructor](arithmetic_control_constructor254.md). Its 27 executing edges and 35 successor branches are bound to the actual register-program catalogue. The exit at 433 begins the following constructor. The [structural source-rank interface](arithmetic_control_source_rank254.md) proves all 28 complete catalogue equalities, including the exit, from explicit tree paths and ranks. The unbounded execution follows from the generic constructor theorem.

The original source run failed with ten maximum-recursion-depth diagnostics while reducing catalogue equalities. It produced no accepted object and did not reach the audit. The successor adds the SourceRank import and replaces the 28 private equality proofs by structural witnesses. The theorem statements, cached target facts, shape definitions, model proof and audit are unchanged; the recorded inverse recovers the complete original source. Both preparations and both actual outcomes remain in [the exact history](results/arithmetic-control-ax-next-constructor254-history.json).

The successor passed its source and [typed audit](arithmetic_control_ax_next_constructor254_audit.lean) in 5.555 and 1.684 seconds with zero warnings. The audit has three named probes and four callers, including arbitrary internal files and `WS = cantor(left, rest)`. Entry and exit facts use `propext`; the execution theorem uses `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-next-constructor254-verification.json) preserves raw output, exact commands and the fresh object/first-provider captures saved before audit. These timings describe this unit, not a general catalogue performance result.

The [independent actual-evidence review](results/arithmetic-control-ax-next-constructor254-review.json) checked all 235 current inputs, the 102-project import closure, six retained Foundation/Mathlib pairs (five direct imports), Init/Omega and both immediate parents. It links the separate original source/guard reviews and the structural-proof successor reviews. The publication builder was prepared by a separate packaging author; proof execution, installation and maintained-default preparation are root-owned. [Publication metadata](results/arithmetic-control-ax-next-constructor254-publication.json) records those roles and the exact selected files.

The two immediate proof parents are generic Constructor run2 and SourceRank run2. Both have genuine source-object and first-provider captures before audit. Older ancestor limitations remain as recorded: the legacy FiniteControlTable evidence lacked those captures, and SourceRank's scope did not revalidate its 137 excluded ancestral units. The [provider proposal](results/arithmetic-control-ax-next-constructor254-provider-proposal.json) preserves the exact selected pairs. Replay requires the recorded caches; this packet excludes compiled objects and makes no clean-checkout dependency-build claim.

The maintained [guard](check_arithmetic_control_ax_next_constructor254.py) changes only its source, audit and provider-proposal default paths. The SourceRank evidence argument remains required. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_next_constructor254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-constructor254-verification.json \
  --source-rank-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-source-rank254-verification.json \
  --output /tmp/fresh-ax-next-constructor-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory checks the source and audit with default proof limits, one thread, 4,096 MiB and a shared 120-second budget. The full AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
