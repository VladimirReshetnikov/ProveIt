# Internal AX implication constructor at controls 460–487

[ArithmeticControlAXConstructor460254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXConstructor460254.lean) proves the actual **460→487** implication-constructor contract for every internal register file in a model of IΣ₁. With both scratch coordinates initially zero, it supplies a positive internal execution time and the complete output file:

- `TW := wim(first(oldWS), oldTW)`;
- `WS := second(oldWS)`;
- every other coordinate unchanged, including both scratch coordinates.

The occurrence instantiates the checked [generic constructor](arithmetic_control_constructor254.md). Its 27 executing edges and 35 successor branches are bound to the actual register-program catalogue. The [structural source-rank interface](arithmetic_control_source_rank254.md) proves all 28 complete catalogue equalities, including the exit, from explicit tree paths and ranks. The exit instruction is `.decnz 1`. The unbounded execution follows from the generic constructor theorem; this result does not compose the surrounding AX branch.

The first actual source and [typed audit](arithmetic_control_ax_constructor460254_audit.lean) passed in 5.224 and 1.655 seconds, with zero warnings. The audit has three named probes and four callers, including arbitrary internal files and `WS = cantor(left, rest)`. Entry and exit facts use `propext`; the execution theorem uses `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-constructor460254-verification.json) preserves raw output, exact commands and the fresh object/first-provider captures saved before audit.

The [independent actual-evidence review](results/arithmetic-control-ax-constructor460254-review.json) accompanies the separate independent source/API/guard review. Root checked all 235 current inputs, the 102-project import closure, six retained Foundation/Mathlib pairs (five direct imports), Init/Omega and both immediate parents. The source and guard author also prepared the publication writer; the embedded reviews retain their own reviewer identities. [Publication metadata](results/arithmetic-control-ax-constructor460254-publication.json) records the selected evidence and this authorship distinction.

The [exact history](results/arithmetic-control-ax-constructor460254-history.json) preserves the source writer, literal inventories, source/guard deltas, preparation, first actual PASS, reviews and reviewer scripts. A root metadata reviewer initially assumed log paths occurred inside command records; it was corrected to use the actual sibling `source.log` and `audit.log` files. The independent source reviewer also corrected a tool-import classification before issuing its receipt. These are metadata-review corrections, not Lean failures or proof replays.

The immediate proof parents are generic Constructor run2 and SourceRank run2. Both have source-object and first-provider captures before audit. Older ancestor limitations remain recorded: legacy FiniteControlTable evidence lacked those captures, and SourceRank's scope excluded revalidation of 137 ancestral units. The [provider proposal](results/arithmetic-control-ax-constructor460254-provider-proposal.json) preserves the selected pairs. Replay requires the recorded caches; compiled objects are excluded from this packet.

The maintained [guard](check_arithmetic_control_ax_constructor460254.py) changes only source, audit and provider-proposal default paths. The SourceRank evidence argument remains required. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_constructor460254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-constructor254-verification.json \
  --source-rank-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-source-rank254-verification.json \
  --output /tmp/fresh-ax-constructor460-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory checks source and audit with default proof limits, one thread, 4,096 MiB and a shared 120-second budget. Full AX, interpreter/Enum comparison and the internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
