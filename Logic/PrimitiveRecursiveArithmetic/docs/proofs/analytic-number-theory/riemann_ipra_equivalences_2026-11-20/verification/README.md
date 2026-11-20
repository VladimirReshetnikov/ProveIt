# Verification receipts

The default Lake target compiles every Lean module in this archive, using Lean 4.32.0 and the Mathlib revision in the manifest. The project was checked on November 20, 2026. The independent arithmetic computations use Python's standard library. `examples.txt` records the outputs of both checkers, including the separate X^5−1 input.

`Audit.lean` imports the project, checks representative types, and prints their Lean kernel axioms. In `lean-audit.txt`, “depends on axioms” describes the Lean metatheory. Internal intuitionistic arithmetic proofs are distinguished by their conclusion type `Prf PRAAx …`. The report states which analytic and finite identifications are supplied as mathematical proofs.

From the archive root, run `lake build` and then `lake env lean verification/Audit.lean`. The exact model and object-language scope of each family are described on page 2 of the report and in the main README.
