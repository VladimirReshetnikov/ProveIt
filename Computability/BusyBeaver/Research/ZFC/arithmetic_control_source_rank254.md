# Structural lookup of catalogue ranks

[ArithmeticControlSourceRank254](../../Lean/BusyBeaver/ZFC/ArithmeticControlSourceRank254.lean) proves a reusable relation between a binary-tree path and its position in the false-first leaf catalogue. `AtRank.bound` bounds that position; `AtRank.lookup` identifies the catalogue entry; `source_of_atRank` derives the complete existing control source from such a witness. Right branches add the left subtree’s leaf count. This constructs no new program and assumes no execution contract.

Two concrete witnesses identify the exact path and instruction at controls **354** (`decnz 1`) and **6423** (`decnz 6`) of `ActualTree254`. The latter proof includes a left-subtree count of 6,329. These are finite source-binding clients, not an all-control benchmark or an internal arithmetic execution theorem. No general speedup, whole AX contract, or PA interpreter-to-enumerator conclusion follows from this unit.

The [audit](arithmetic_control_source_rank254_audit.lean) has five named probes and five typed callers. The [selected second run](results/arithmetic-control-source-rank254-verification.json) passed in 0.624 seconds for source and 0.429 seconds for audit, with zero warnings. The bound theorem has no axioms; the other four reports contain only `propext`. The new source object and actual first provider were captured before audit and remained unchanged afterward.

The first actual source check failed at two residual `Option.map` goals, before audit. The [repair record](results/arithmetic-control-source-rank254-source-repair.json) preserves the original source/audit/guard and adds exactly two `rfl` steps after rewriting. The theorem statements, witnesses, audit and default proof limits are unchanged. Its original “proposed, not executed” status records when the repair was prepared; the separate actual second-run record establishes success. The [history](results/arithmetic-control-source-rank254-history.json) preserves both preparations, the original failed attempt and raw output, the successful second attempt and logs, all available root/peer reviews and reviewer sources. The maintained source uses the checked successor bytes under the canonical module filename.

The [existing-evidence review](results/arithmetic-control-source-rank254-review.json) checks all 82 current inputs, 33 project providers, no external project boundary, and Init/Omega. The older `FiniteControlTable254` parent did **not** record a source-pass object or first provider before audit. Its current provider resolution is checked without inventing that historical capture. The 32 selected ancestor identities are traced to the recorded 169-unit integration; the other 137 ancestor modules were not revalidated. This limitation remains explicit in the actual record and review.

The maintained [guard](check_arithmetic_control_source_rank254.py) changes only its source and audit default paths. With the exact historical compiler and provider caches available, preparation from the repository root is:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_source_rank254.py \
  --repo "$PWD" \
  --table-evidence Computability/BusyBeaver/Research/ZFC/results/finite-control-table254-verification.json \
  --output /tmp/fresh-source-rank-preparation \
  --prepare-only
```

Preparation makes no compiler or version query. Omitting `--prepare-only` checks only this source and audit in a fresh output directory, with one thread, 4,096 MiB, a shared 120-second budget and default proof limits. No dependency build or download occurs. Compiled caches are excluded from publication; this is not a clean-checkout build certification. Maintained-default preparation is recorded separately after installation.

The underlying register program is Mira-Cult’s, imported through Jeff Ketchersid’s verification and Andrew James Wade’s compiler framework. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) retains its attribution and provenance.
