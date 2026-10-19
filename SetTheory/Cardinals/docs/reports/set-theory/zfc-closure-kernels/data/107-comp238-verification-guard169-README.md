# Guard for combining the two 239-state constructions

This directory adapts the coordinated239 guard proof to the accepted Boundary239 table from `ZFC_239_State_Construction_2026-10-19`. It is the input-side compatibility obligation needed to apply the 169-to-80 reduction to that independently shortened source.

Run from the package root:

```sh
python3 -B verification/guard169/certify_guard169_A.py \
  --table inputs/boundary239_old.tm \
  --sites machines/sites_logical.json \
  --output-dir replay-guard169
```

Alternatively supply absolute paths. Python 3.10+ and the standard library suffice. The final result must have status `PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD`. Assertions must remain enabled. The main `reproduce.py --full` runs this check and compares its complete per-case and per-visit results with the included evidence.

`symbolic_runtime.py` and `independent_runtime.py` are unchanged copies of the attributed coordinated239/incoming80 mathematical checker. The driver repeats its exact source-tree structural checks with the new source pin; it does not bypass those checks. Both literal input files and both helper files are pinned. `PROVENANCE.json` specifies every changed input and validation premise.

The runtime proof represents all nine primary registers, extra gap, and first spare value by independent arbitrary natural parameters, and the remaining spare sequence by an arbitrary finite list. At every state169 visit the driver checks the rightward orientation. Whenever it reads one, the normalized run containing that cell has affine length with constant term at least two. All coefficients are nonnegative. This implies that the immediately right-hand cell is also one for every assignment of the parameters.

Unary accelerations cannot hide state169 because neither of its rows is a self-loop. The separately rederived one-block traces and entries of all four list traversals exclude state169, so list induction cannot hide it either. Every whole-tape instruction endpoint and positive-clock assertion remains enabled.

The source calibration and the local four-block substitution are separate proof components. This audit proves the runtime guard and the prescribed finite initialization guard. It is ordinary executable mathematical evidence, not a Lean/Rocq kernel theorem.

The original inherited driver docstring shows an older usage example. The invocation above supplies the correct files for this adaptation.

## Completed result

The proof passed all 8,386 guarded cases in 2,247,513 symbolic rules and covered all 478 rows. There are 32 symbolic state169/read1 visits, each with one-run constant at least 23; the required lower bound is two. The exact blank prefix has 409,691 steps and six further checked visits. The minimum constant instruction duration is 13.

The main `report.tex` explains the proof. The three JSON receipts under the package-root `evidence/guard169/` record the complete execution. This README was adjusted for the combined package layout; the driver and its pinned engine/helper retain their recorded bytes.
