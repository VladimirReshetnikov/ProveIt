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

## Pell index and bootstrap arguments

| Module | Before | After | Lines removed |
|---|---:|---:|---:|
| `NativePellFirstIndex` | 108 | 104 | 4 |
| `NativePellPower` | 181 | 180 | 1 |
| `NativePellStepDown` | 248 | 230 | 18 |
| `NativePellBootstrap` | 685 | 671 | 14 |
| **Total** | **1222** | **1185** | **37** |

The proof changes reuse the existing positivity lemma, standard product
order bounds, `Or.imp`, integer divisibility closure and the natAbs square
identity. `omega` handles mixed natural/integer linear bounds directly,
removing repeated manual cast bridges. Definitions, imports, theorem
statements and their sign/range assumptions are unchanged.

`alternate_encoding_research` authored this chunk and directly observed
zero exits for all four final source/olean checks in dependency order,
all four existing focused check modules and the `FirstPellCarrier`,
`NativeBinaryScale` and `NativeHalfBinomial` clients. The axiom checks cover
46 theorems and include signed-quotient, ordinary Pell and port-box examples.
Only standard axioms occur. The unchanged `NativeBinaryScale` source retains
its existing unused-variable warning.

ROOT read all changed proof hunks and checked the final source hashes.
`v_finite_full_static` independently reviewed every changed hunk in context,
including all four divisibility sign cases and the natAbs alternatives,
and reported PASS. These checks do not assert a complete library rebuild.

## Primitive-recursion congruence

The placed proposal's `patches/pr-congruence.patch` is now integrated in
the maintained `PRCode`, `ScalarPRCode` and `ScalarPROptimizer` modules.
Their lengths decrease from115/87/153 to105/76/140, removing34 lines.
Explicit `simp only` rewrites the supplied base and step equalities under
`Nat.rec`, replacing three repeated congruence inductions. Program syntax,
evaluators, optimizer definitions and the two returned `.prec` program values
are unchanged; only their correctness proofs change.

`intake_e13` directly observed zero exits for all three final module/olean
checks in dependency order, the `ScalarPRRepresentation` client, existing
`ProgramOptimization` and `CompilerAxioms` checks, and two focused `rfl`
checks of the returned program values. ROOT read all three complete final
modules and the patch, including its source note and validation caveat.

The shorter scalar constructor proof uses `[propext, Quot.sound]` instead of
the original empty axiom set. The vector constructor adds `Quot.sound` to
its earlier `[propext]`; the optimizer retains its three standard axioms.
This is the documented function-extensionality cost of rewriting under a
binder. There are no new axiom declarations or unsafe assumptions, and all
printed axiom sets contain only standard Lean axioms.

## Shared assignment transport

The proposal's `assignment-map.patch` is integrated in `Representation`.
Its shared `natAssignment_comp_map` lemma replaces five repeated function
equalities in reindexing, conjunction and disjunction. The quartic compiler's
private assignment wrapper also delegates to this common lemma. The two
modules decrease from260/449 to235/448 lines, removing26 lines including
the new shared lemma. Witness counts, expressions, evaluators and all earlier
theorem statements are unchanged. The compiler wrapper is49 bytes longer,
while the combined change removes731 bytes and the duplicated argument.

`alternate_encoding_research` directly observed zero exits for both final
module/olean checks, the `ArithmeticRepresentation`, `EquationFromRep` and
`NaturalSimplifier` clients, existing `RepresentationSize` and `QuarticCost`
checks and two axiom audits. The shared lemma uses only `Quot.sound`; all
other printed sets are standard axioms. ROOT read the complete final
representation module, the compiler wrapper in context and both diffs.
