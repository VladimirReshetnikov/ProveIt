# Internal AX accumulator push at controls 301–327

[ArithmeticControlAXACPush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXACPush254.lean) proves the actual **301→327** accumulator push. For every internal register file in a model of IΣ₁, with S1=S2=0 initially, it supplies a positive internal execution time and this complete file:

- `TW := oldAC`;
- `WS := cantor(oldTW, oldWS)`;
- all other seven coordinates unchanged, including AC and both scratch coordinates.

The copy/restore tail **320→327** has an exact-time contract: `7 * oldAC + 2` internal steps. It requires only S1=0, permits arbitrary TW, and sets TW to `oldTW + oldAC` while retaining every other coordinate. These unbounded contracts instantiate the checked [generic CopyBack and argument-push contracts](arithmetic_control_copy_back254.md); no finite trace or standardness premise replaces them.

The occurrence binds 26 executing instruction edges and 34 successor branches. Its proof first records 27 complete catalogue-source equalities, including the exit. The shape proofs reuse their edge projections and a finite target-path adapter. The cached facts change proof construction; the model section, public statements and audit remain identical to the preserved uncompiled draft. No performance comparison with that draft is claimed.

The [typed audit](arithmetic_control_ax_ac_push254_audit.lean) contains six named axiom probes and eight callers, covering arbitrary retained coordinates, both scratch coordinates, the tail and the full push. The **first actual attempt**, stored in a directory named `run2`, passed in 26.604 seconds for source and 1.846 seconds for audit, with zero warnings. No `run1` compilation occurred. The three control reports use `propext`; the three file/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-ac-push254-verification.json) preserves the exact commands, logs and fresh object captured before audit.

The [existing-evidence review](results/arithmetic-control-ax-ac-push254-review.json) checks all 225 actual inputs and their preparation counterparts, the exact 99-project import closure, six cached Foundation/Mathlib pairs (five directly imported), Init/Omega, current first-provider resolution and the saved fresh object. Its separate source review independently checks the 27 cached source equalities and all 34 finite target and consumption facts against the full literal tree. The source/guard authors, reviewer and root-owned proof execution are distinguished; the reviewer subsequently prepared the publication builder.

[The history](results/arithmetic-control-ax-ac-push254-history.json) preserves the uncompiled v1 source/guard, source and provider inventories, the cached-source successor and its exact proof-only diff, source reviews, preparation, actual PASS, raw logs and root receipts. A reviewer-only metadata correction to false-padded path consumption is also preserved. It changed no Lean source or actual evidence. No failed proof attempt or unavailable evidence is invented.

The [provider proposal](results/arithmetic-control-ax-ac-push254-provider-proposal.json) remains the exact historical v1 proposal. The executed guard's explicit source hash and default path select the checked v2 source; the successor record makes that distinction explicit. Its immediate CopyBack parent records both source-object and first-provider captures before audit. Earlier ancestor evidence retains its original scope. Replay requires the exact historical cached providers; compiled caches are excluded, and no clean-checkout dependency rebuild is certified. The retained `HFS.Seq` pair supplements the five directly imported external boundaries.

The maintained [guard](check_arithmetic_control_ax_ac_push254.py) changes only source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_ac_push254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --copy-back-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-copy-back254-verification.json \
  --output /tmp/fresh-ax-ac-push-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit with default proof limits, one thread, 4,096 MiB and a shared 120-second budget. The later constructor, complete AX branch, interpreter/Enum correspondence and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
