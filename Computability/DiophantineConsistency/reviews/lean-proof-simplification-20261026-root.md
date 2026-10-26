# Lean proof simplification, 26 October 2026

The active objective is to shorten and simplify existing Lean proofs.
The baseline for this series is `7fa06d530df54d4aeb2e18027409df082234c69e`,
merged from the successfully fetched `origin/main`. Further reductions remain
open. Equation source, PDF and coefficient recipes are outside these edits.

## Population and coefficient bounds

| Module | Before | After | Lines removed |
|---|---:|---:|---:|
| `MaskPopulation` | 162 | 155 | 7 |
| `NativeMaskPopulation` | 110 | 96 | 14 |
| `SelectiveCoefficientBounds` | 234 | 211 | 23 |
| `SplitCoefficientBounds` | 122 | 117 | 5 |
| **Total** | **628** | **579** | **49** |

All changes are inside existing proof bodies. Imports, definitions, theorem
statements and hypotheses are unchanged. The 31-coordinate half-base bound
now specializes the general theorem already in the same module. Standard
List/Finset lemmas replace the range-sum induction and filter extensionality
proof. `Nat.mul_ofDigits` replaces the repunit scaling induction, and the
binary-shift and power-product lemmas simplify the remaining arithmetic.

ROOT authored these changes and rebuilt all four module oleans with
`lake env lean SOURCE -o .lake/build/lib/lean/DiophantineConsistency/MODULE.olean`.
Each final command returned zero. ROOT then ran these four existing checks;
each returned zero:

```text
lake env lean Computability/DiophantineConsistency/Lean/checks/MaskPopulation.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeMaskPopulation.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SelectiveCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SplitCoefficientBounds.lean
```

These check actual mask examples, including selected position zero, signed
coefficient collisions, the minimal digit cap and a rounded-up base. Their
axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.
An attempted direct triangle-inequality term exceeded the default elaboration
budget; its original explicit proof was retained. Heartbeat limits are unchanged.

`v_finite_full_static` independently read all four final sources and every
changed proof, checked the unchanged interfaces and `git diff --check`, and
reported PASS. Independent source checks for the first three modules and a
focused `SelectiveCarry` example/axiom check also returned zero. ROOT's final
rebuild and focused check cover the final `SplitCoefficientBounds` source.

The environment is the repository's Lean 4.32.0 and pinned mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, using its existing dependency cache.
The changes introduce no axiom declarations, `sorry`, `admit`, or native-decide
trust extension. A complete library rebuild is not claimed.

## Input specialization and positive domains

`Polynomial` decreases from125 to116 lines and `PositiveDomain` from34 to32,
removing11 proof-body lines. `Fin.comp_cons` and `Fin.cons_self_tail` replace
coordinate-by-coordinate function equalities. The positive-domain proof uses
the integer-to-natural cast equality pointwise. All existing definitions,
imports, statements and premises are unchanged.

`intake_e13` authored this separate chunk and directly observed zero exits
for both changed module/olean checks, the `ZFC` and `PositiveZFC` clients,
and a focused axiom audit of the specialization and positive-domain results.
The printed axioms are standard Lean axioms only. ROOT read both complete
final files and every changed hunk, confirming the interface and witness maps.
These are author tool observations; no separate raw log files or complete
library rebuild are asserted.
