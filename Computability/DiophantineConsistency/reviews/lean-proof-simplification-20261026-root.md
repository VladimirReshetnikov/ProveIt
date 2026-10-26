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

## Core list lookup lemmas

The proposal's `list-library.patch` replaces seven private inductions in
`AnnotatedProofChecker`, `AnnotatedRename`, `AnnotatedBound`,
`AnnotatedRuleSide` and `AnnotatedAssumption` with `List.mem_of_getElem?`
and `List.getElem?_of_mem`. The five files decrease from1286 to1246 lines,
removing40 lines and1553 bytes. Every wrapper signature and private name is
retained, and all checker/parser definitions and premises are unchanged.

`v_finite_full_static` read the complete five sources and exact core lemma
signatures, applied only those proof replacements, and directly observed
14 zero exits: the five module builds, four direct clients (`ProofCode`,
`RenameCode`, `BoundLocal`, `Line`) and five existing focused check files.
The build logs are empty; the focused checks retain their passing executable
controls and standard-axiom reports. ROOT read every changed declaration
and the checker axiom output. No archive script or whole-library build ran.

The first six committed groups in this review remove197 maintained Lean source
lines across20 modules, including the shared assignment lemma. The general
proof-simplification goal remains active; these are iterative checkpoints.

## Reuse unconditional packing bounds

`SplitWordBounds.weak_cap_packing` and its `GapWordBounds66` counterpart now
obtain source positivity, both low-mask bounds and both packed-word signs
from their already-proved `unconditional_word_bounds` theorems. This removes
14 lines, reducing the two modules from376/261 to369/254 lines. The weak cap,
target bounds, injectivity, scale and nonnegativity assumptions are unchanged,
as are all upper-packing and final rank-cap steps.

ROOT read the sources and authored this change. Both module/olean rebuilds
and both existing focused check files returned zero; all printed theorem
axioms are standard. `v_finite_full_static` independently read the helper
contracts and complete changed packing proofs and reported PASS.

## Mask lookup and predecessor powers

`LowMaskCoding` decreases from405 to395 lines and `MultiTargetCarry` from273
to263, removing20 lines. Support sums reuse `Finset.filter_mem_eq_of_subset`,
the unique-coordinate proof uses the supplied injectivity directly, and three
predecessor-power identities use `Nat.sub_add_cancel` with their existing
positive-exponent hypothesis. Definitions, imports, theorem statements and
all range, support and injectivity premises are unchanged.

`v_finite_full_static` directly observed nine zero exits: both rebuilt modules,
both existing focused checks and five clients (`MaskPopulation`,
`NativeQuadraticSource52`, `NativeSparseBounds52`, `SelectiveCarry`,
`SparseBorrowCarry`). All printed axioms are standard. ROOT read all six
changed proof bodies; `alternate_encoding_research` independently reviewed
the changes in context and reported PASS.

## Shared finite-residual compiler facts

The review packet's `finite-residuals.patch` is integrated as a36-line
`CompilerSupport` module and proof replacements in `DAGQuartic`,
`NaturalDAGQuartic` and `QuadraticRegisterSystem`. It shares evaluation and
degree bounds for finite sums of squared residuals, plus natural-assignment
transport. The three existing modules decrease from285/293/170 to257/264/158
lines; including the new helper, the net saving is33 lines and1612 bytes.

Every existing theorem statement, topology/nonnegativity hypothesis,
expression, circuit and witness definition is unchanged. The helper imports
`QuarticSyntax`; it is imported by the DAG compiler, preserving acyclic layering.
The source proposal is in
`docs/incoming/lean-proof-simplification-review-2026-10-26.zip`.

`alternate_encoding_research` directly observed ten final zero exits: four
module/olean builds, `QuadraticNatPairing` and `QuadraticDivMod` clients,
three existing compiler focus checks and one helper/API axiom audit.
The checks include signed negative intermediates, nonzero rejection, natural
compiler restrictions, witness counts and zero-denominator rejection.
All eight replaced public results retain their original standard-axiom sets.
ROOT read the complete helper and every changed client proof;
`v_finite_full_static` independently reviewed all helper and client changes
and reported PASS.

Across all nine groups, this series removes264 maintained Lean source lines,
including36 lines for the new shared helper. Larger generated-steps and
scanner refactors remain under review; the iterative goal is active.
