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

## Generated Steps: maintained generator integration

ROOT ported packet a's checked indexed helpers into the maintained shared
`generate_split_recipe_steps59.py` renderer. The existing Gap wrapper, exported
Python globals, input loading, `rhs` function, public theorem headers and
`naturalRegister` definition are retained. Labels come from the pinned natural
DAGs, with zero meaning no asserted power specification. Each circuit gets one
closed `PowerStep` certificate and applies the existing `run_power` theorem;
the certificate alone has a scoped12000000-heartbeat allowance.

Before any project Python execution, `intake_e13` and `v_finite_full_static`
independently read the full exact-final four-file executable closure, both
pinned raw natural inputs and the available read/write routes. Both returned
static PASS with no findings. ROOT separately read the whole closure, the
generic Lean contracts and the register-generator consumers. Reviewed SHA256s:

| File | SHA256 |
|---|---|
| `tools/generate_split_recipe_steps59.py` | `d0a99e733af59177d9fe24624bcf6fa50fe11bef700ed025d05cf252bb7510c4` |
| `tools/generate_gap_recipe_steps66.py` | `bbffdc727abbc33002b32df1b1cdb1fb4bbc01fba0653271cf812083ef716e08` |
| `tools/generate_split_circuit59.py` | `ac616ed886bf8616a8f671e8af3382e148226a1958eef7b03b043bed7ce5a789` |
| `tools/generate_gap_circuit66.py` | `2e9459e55f527e093af47b4be09a293f79b56e1668799c7123e25c989dd17621` |

The raw natural input pins are `cb0caa3a14370e9a5d43be9cabbfef86f92481301b09f4fd7bc7c19f550804db`
(Split,515 nodes,base36) and `be7d9e1285a1cf674978058c3b1be2f27a17af9c0d0bdc6e4f8310481a40d001`
(Gap,484 nodes,base20). Imported circuit writers remain behind `__main__`
guards. Gap imports the Split template and therefore reads both raw inputs.

ROOT releases the exact reviewed Steps entrypoints for `python -B SCRIPT`
generation and `python -B SCRIPT --check` / `python -B -O SCRIPT --check`.
Generation may write only the respective existing maintained Steps Lean file;
the checks compare its complete text. `-B` prevents import-cache writes, and
explicit `require` checks remain effective under `-O`. No archive application,
source-rewriting candidate script or circuit generator entrypoint is released.
This static release does not claim that the regenerated maintained Lean files
or their clients have passed; those checks follow generation.

Both actual generations and all four normal/optimized `--check` invocations
returned zero. The regenerated Split/Gap files decrease from3445/3122 to
2565/2356 lines, removing1646 lines and98239 bytes including all helpers and
label tables. All1192 public theorem statement texts are unchanged modulo
whitespace; both `naturalRegister` definitions are exact-equal. The maintained
proof code equals packet a's kernel-checked full candidates modulo provenance
comment and whitespace. Neither DAG, raw JSON nor evaluator data is changed.

Both final maintained Steps modules were rebuilt with `lean -j1` and named
oleans, returning zero with empty diagnostics. ROOT's fresh all1192-theorem
`#print axioms` audit also returned zero: every result uses exactly the
standard `[propext, Classical.choice, Quot.sound]` set. The prechange existing
focused checks report the same set for their representative results.
The generator and two regenerated modules are committed as `79bc166a51`.
Downstream client validation is recorded below once complete; no compile-time
speedup is claimed. Full candidate checks peaked at4568828/4828612KiB RSS.

## Nine-coordinate source-existence transport

`alternate_encoding_research` extracted a39-line `FreeCarrierCoordinates`
module with an evaluator-parametric positive tuple theorem and a
predicate-parametric successor/predecessor theorem. Both Split and Gap source
existence modules reuse these facts. Including the entire helper,295 lines
become269, removing26 lines and30 bytes. All existing definitions, public
theorem statements, coordinate ordering and positivity premises are unchanged.
The internal CRT index remains an unrestricted natural number; its positive
external coordinate is `j+1`. No additional coordinate wrapper definitions
are introduced. ROOT read the full helper and both changed proof sections.

All eight final checks returned zero: three module/olean builds, the two
existing focused check files, both `SplitNineSource59` / `GapNineSource66`
direct-client sources and a six-result axiom audit. The focused checks retain
the all-one positive/all-zero natural tuple identities and the internal
`j=0` case. The rewritten public results retain the standard-three axiom set;
the generic successor theorem uses only `propext` and `Quot.sound`.
The source change is committed as `32b108f214`.

The complete generated-Steps validation chain subsequently passed26/26 calls:
14 maintained module/olean builds and12 existing focused checks. Builds cover
both Steps, Registers, Translations, Recipes and PositiveRecipes, plus
`GapCircuitTail66`, `GapCircuitDegree66`, `GapFinalizerDegree66` and
`GapPolynomialDegree66`. Checks cover both Steps/Registers/Translations/
Recipes/PositiveRecipes, `GapCircuitTail66` and `GapDegree66`.
`v_finite_full_static` observed every zero exit; ROOT independently read all26
time receipts and the89 focused axiom reports (including one axiom-free
result). All reported axioms are standard. Unchanged register/recipe sources
emit existing style warnings; no substantive failure or retry occurred.
Final maintained Steps runs took52.88/45.91 seconds and peaked at4828064/
4567316KiB RSS, respectively. No performance improvement is asserted.

`v_finite_full_static` also independently read immutable `32b108f214`, the
whole coordinate helper and all four changed proof contracts, returning PASS
with no findings. This review required no additional source edits or rebuilds.

## Local radix, convolution and finite-selector proofs

`intake_e13` adapted the remaining packet f proposals in `SelectiveCarry`,
`NativeCyclicConvolution`, `NativeRadixDigits` and `ArithmeticFiniteSwitch`.
ROOT suggested the two additional `Nat.one_lt_two_pow` applications in the
carry module and read all final changed proofs in context. The four modules
decrease from204/258/108/32 to194/253/104/29 lines, removing22 lines.
Every original signature, import, bound/mask premise and executable program
constructor is retained. The selector changes only the `ofEq` proof.

The packet's combined convolution simplifier initially failed twice on the
nested-sum ordering. The final proof explicitly distributes the sums, applies
`Finset.sum_comm` and then normalizes multiplication. All four final named
module/olean builds, four existing focused checks and four direct clients
(`SelectiveCoefficientBounds`, `NativeStencil54`, `NativeVariableMask`,
`AnnotatedAxiomDispatch`) returned zero. Generic zero/successor selector
`.val` constructor equalities are still `rfl`. Baseline/final axiom sets of
the six audited declarations are identical standard Lean axioms.
The source changes are committed as `2effe6f291`.

`alternate_encoding_research` independently read all580 final source lines,
the changed proof contexts and the `Realizes.ofEq` / `DirectScalar.ifEq`
definitions. It returned static PASS with no findings and reauthenticated all
four final hashes. In particular, `ofEq` returns the supplied program's `.val`
verbatim; the changed certificate cannot alter either selector constructor.

These three additional groups remove1694 maintained Lean lines, including
every new helper and label table. Together with the previous nine groups,
this iteration series removes1958 lines. The decimal equation artifacts
are unchanged. The iterative proof-simplification goal remains active.

## Shared Pell ratio error factor

The newly merged `lean-proof-simplification-new-2026-10-26.zip` supplies
`patches/01-pell-factor.patch`. `v_finite_full_static` applied its two-file
proof refactor: a positive-real-factor upper estimate lives in the existing
HTP `Diophantine/Paper1980/PellRatio90` module, and the ordinary/native
wrappers specialize factors1/2. Every old signature and premise, including
the ordinary wrapper's `hYr` argument, remains unchanged. Existing recurrence,
input and ratio definitions are untouched. No consistency-layer import is
added to the lower HTP module.

The paper module grows from472 to478 lines and the native module shrinks
from244 to161. Including the whole generalized proof and both wrappers,
the net reduction is77 lines and3654 bytes. ROOT read the whole changed
proof in context and compared all19 old theorem statement texts; they are
unchanged. `alternate_encoding_research` independently read all639 final
source lines, the whole patch and the scaling/positivity contracts, reporting
PASS on the exact frozen source hashes with no findings.

Both changed modules and `PellRatio3` first passed. The `Pell90` client then
failed before elaboration because `Bootstrap90.olean` was missing; its log is
retained separately. The minimal missing cache closure was only `System90`,
`Bootstrap90` and `PellExponent90`. All three unchanged prerequisites built
successfully, then the unchanged `Pell90` client passed with an empty log.
No source repair or raised proof limits were needed.

All12 final verification calls returned zero: two touched module/olean
builds, three direct clients (`PellRatio3`, `Pell90`, `NativePopulationLower`),
the three cache prerequisites, two existing native focused checks and two
axiom audits. Five existing public axiom reports are byte-identical before
and after; the new helper uses only standard Lean axioms. ROOT independently
compared the two public audit logs and read the helper report.
The source refactor is committed as `8ca6455829`.

Across the four additional source groups, this continuation removes1771
net Lean lines, including all helper costs. The reviewed iteration series
now removes2035 net lines across both affected library locations. New packet
intake ranks signed-root recovery and internal natural-case reuse next;
their archived compilation evidence is recorded as pending in `ADOPTION.md`
and has not been substituted for maintained-tree checks. The goal stays active.
