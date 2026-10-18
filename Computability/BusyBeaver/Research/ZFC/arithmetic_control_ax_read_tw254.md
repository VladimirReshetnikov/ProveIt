# Internal AX read into TW

[ArithmeticControlAXReadTW254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXReadTW254.lean) proves the actual AX read at catalogue controls **181→195**. In any internal model of IΣ₁, with both scratch coordinates initially zero, it supplies a positive internal execution time and the complete output register file:

- `TW := oldTW + first(oldPL)`;
- `PL := second(oldPL)`;
- every other coordinate retains its old value.

The input TW, PL, and all other register values are arbitrary elements of the arithmetic model. The paired-stream client accepts `PL = cantor(x, rest)` and returns `TW = oldTW + x`, `PL = rest`. The proof instantiates the existing `ReadShape` theorem with all fourteen actual instruction edges and nineteen resolved successor equalities. It adds no execution premise or new induction.

The [typed audit](arithmetic_control_ax_read_tw254_audit.lean) contains seven named axiom probes and twelve callers. They cover the entry and exit, both changed coordinates, arbitrary other-coordinate preservation, both runtime contracts, cache/WS/scratch preservation, and the zero-TW specialization. The first actual source/audit run passed in 22.873 and 2.214 seconds, respectively, with zero warnings. The first two reports use `propext`; the other five use only `propext`, `Classical.choice`, and `Quot.sound`. See the exact [verification record](results/arithmetic-control-ax-read-tw254-verification.json) and [independent review](results/arithmetic-control-ax-read-tw254-review.json).

The original draft used direct reductions of the catalogue resolver. Before any ReadTW compilation, those nineteen proof bodies were replaced by the finite actual-tree walk helper already used in the constructor unit. The helper uses the checked program/tree identity, `resolve_source`, and `source_injective`; its literal targets are unchanged. No failed ReadTW proof run preceded this PASS. The [history](results/arithmetic-control-ax-read-tw254-history.json) retains that uncompiled draft, the proactive helper repair, both source versions, the exact executed guard, raw preparation and successful run records/logs, source-only reviews, and root receipts. It also preserves the root's reported initial metadata-inspection schema error, which did not run a compiler.

The guard selects 96 project providers from the exact checked Pair parent. It verifies five directly imported Foundation/Mathlib boundaries, separately retains the inherited `HFS.Seq` source/object pair, and binds Init/Omega. The Pair parent recorded its source object before audit but did not have the later separate first-provider field; its recorded search path is resolved now and that limitation remains explicit. ReadTW records both its fresh source object and its actual first provider before running the audit.

The maintained [guard](check_arithmetic_control_ax_read_tw254.py) changes only the source, audit, and provider-proposal default paths from the executed guard. Replay requires the exact historical cached providers in [the provider proposal](results/arithmetic-control-ax-read-tw254-provider-proposal.json) and verification record. No compiled caches are distributed, and this packet does not certify a clean-checkout dependency build. Preparation uses no Lean or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_read_tw254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --pair-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-pair254-verification.json \
  --output /tmp/fresh-ax-read-tw-preparation \
  --prepare-only
```

After reviewing that preparation, omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, a 4,096 MiB memory limit, and one shared 120-second budget. This unit covers only controls 181→195; the complete AX branch, interpreter/Enum comparison, and internal binary consistency equivalence remain separate obligations.

The shared register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
