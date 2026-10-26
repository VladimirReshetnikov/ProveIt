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

## Shared signed-root recovery

Packet m's finalizer refactor is adopted as `025c99b12c`. Both finalizer
proofs now recover the actual signed rational roots through their integral
numerators and share separated root recovery in `NearSquareFinalizer`.
The exponent-nonzero hypothesis is explicit in the rational integrality
helper; scale/weight nonzero and radicand separation remain explicit in the
shared root theorem. The two old wrappers preserve every original premise.
All20 existing theorem statements, imports and three norm/value definitions
are unchanged. Including both helpers/wrappers,432 lines become386,
removing46 lines and2672 bytes.

`v_finite_full_static` read and implemented the exact packet hunks, observed
ten final zero exits (two module builds, three direct clients, three existing
focused checks and two axiom audits), and reauthenticated the final hashes.
The clients are `FreeCarrierDegree`, `GapCircuitTail66` and `MarginSeparation`.
The exact existing focused checks are `NearSquareFinalizer`, `MarginFinalizer`
and `MarginSeparation`; `RatioMarginFinalizer` was not run in this scope.
Focused controls cover all four signed sums, zero/negative margins,
nonsquares, divisibility and the excluded equal-radicand separation.
The eight existing public axiom reports are byte-identical; both helpers use
only standard Lean axioms. ROOT read the whole changed proof and rational
denominator argument. `alternate_encoding_research` independently read both
entire final sources, diff and library contract, reporting PASS with no findings.

## Internal natural cases for zero sums and products

Packet l is adopted as `f7794ed51a`. The two public zero-characterization
proofs reuse `InternalSat.nat_zero_or_succ`, removing inductions that discarded
their induction hypotheses. The now-unused private `zeroSumStage` and
`zeroProductStage` formulas/specifications are deleted; ROOT checked that
they had no remaining maintained-source references. Public signatures,
ZF/membership premises, `cancellationStage`, `additionCancellationForm` and
the no-zero-divisors instance are unchanged. The two modules shrink from
118/60 to96/40 lines, removing42 lines including the explicit imports.

`intake_e13` observed seven final zero exits: both named-olean module builds,
`ObjectMultiplicationLaws` / `ObjectResidualSquares` clients, the existing
`ObjectAdditionCancellation` / `ObjectResidualSquares` checks and the
theorem/inferred-instance axiom audit. The affected old public axiom sets
remain the same standard three. An initial audit guessed a nonexistent
autogenerated instance name; an explicit inferred-instance query replaced
that metadata query without changing maintained code.

ROOT read both full diffs and the actual internal case theorem. Independently,
`v_finite_full_static` read both full sources and the theorem's `omega_ind`
derivation, returning PASS on the exact frozen hashes. The case theorem is
valid over the entire internal omega of arbitrary `ZFAxioms` models,
including nonstandard elements; no external-natural case assumption is used.

## Shared pairing-certificate projections

Packet m's three pairing sections are adopted as `1529520379`. ROOT read
all three original modules and the projection/finite-tuple contracts, then
ported only the two helper proofs and seven `ofIff` proof replacements.
The modules shrink from88/158/150 to94/139/136 lines, removing27 lines
including both helpers. No import or global simplifier attribute is added.

All14 final Lean calls returned zero: three touched module builds, six direct
client rebuilds (`RegisterNatPairing`, `ScalarPRRepresentation`,
`AnnotatedCodeGraphs`, `AnnotatedSyntaxGraphs`, `QuadraticListHead`,
`ObjectPredecessorSyntax`), the existing `QuadraticRegisterSystem` /
`QuadraticRegisterComposition` checks, seven-record equality audit and
old/new helper/public axiom audits. ROOT reconstructed all seven original
constructors from the actual prechange HEAD; each complete original record
equals the new record by `rfl`. This checks expression syntax and witness
layout, rather than only numerical counts. The seven public axiom reports
are byte-identical; both new helper reports contain only standard axioms.
The existing focused checks retain nil-output and zero-denominator controls,
degrees, witness counts and binary-operation counts.

`alternate_encoding_research` independently read all369 final source lines,
the whole diff, original constructor checks and `Rep.ofIff` / tuple contracts.
It returned PASS with no findings on all three frozen hashes. Program,
row, port, system, predecessor and nil data are unchanged.

Together these three groups remove115 maintained Lean lines including all
helper costs. The reviewed iteration series now removes2150 net Lean lines.
ROOT also checked all86 existing public definition/theorem headers across
the seven touched modules; their statement texts are unchanged. Packet ZIPs
were retired during placement, so current adoption references now use the
placed h/l/m/n/o/p directories. The equation artifacts remain unchanged and
the iterative goal stays active.

The historical next-target audit, before `4de06108b3`, found a stale upstream adoption row:
`NativeCoefficientBounds` is still the679-line original, byte-identical to
packet d's baseline (`82f03eecd673b5f72a02d1b2c27ea194f46f94b6bcb445cfd26073d9593bf365`).
`intake_e13` read the whole maintained source, d's full candidate and the
coefficient/mask contracts. The127-line d candidate was compiled in the packet
and preserves all eight public headers and data; its integration and fresh
dependent checks remain pending. The adoption row now states the actual
maintained status at that checkpoint. Its local2M-heartbeat proof and recorded128.05-second
packet run should not be confused with h's distinct122-line/4M alternative
or h's single-host24.42/111.37-second before/after measurements. A source
maintenance reduction is available; no speed improvement is claimed.

## Shared coefficient-envelope proof

`intake_e13` subsequently ported packet d's complete127-line candidate,
adopted as `4de06108b3`. The module decreases from679 to127 lines, removing552
lines. The envelope definition, all coefficient/mask/support constants, all
eight public theorem signatures and the four nonnegativity assumptions are
unchanged. One generic proof handles the22 row cases with the same seven
scalar inequalities and a local2000000-heartbeat allowance. ROOT read the
complete changed proof and data contracts.

The named module build, existing `NativeCoefficientBounds` focused check,
and fresh `NativeNineSource52` / `NativeNineEquation52` client builds all
returned zero. Baseline/final audits of all eight public theorems returned
zero with identical axiom sets: `published_height_eq` uses `propext`, and
the other seven use the standard three. No cache gap or proof repair arose.
The module build took160.69 seconds and peaked at2139032KiB RSS; its olean
grew from1372672 to3686520 bytes. The adopted source SHA256 is
`159c50406a6a4745121f8d1aff2dce77ff459a8e6c187d95516d81effae159fc`.
This reduces maintained source duplication while increasing compiled size;
no elaboration-speed improvement is claimed.

A separate `/tmp` prototype proved the repeated scalar bounds once and
reused them across rows. Its147-line source passed one kernel build in170.32
seconds, peaking at1974072KiB RSS and producing a4953664-byte olean. An earlier
invocation was rejected by the source-root check before elaboration. The
prototype is not adopted: it has longer source and a larger proof object,
with no demonstrated checking advantage. Its observed lower RSS and longer
build time are individual measurements, not controlled comparisons.
Maintained source/cache bytes
were unchanged during this experiment; no further prototype build followed.

## Shared raw-parent and tree-decoder invariants

`v_finite_full_static` implemented packet n as `2ed7cc3ebb`. `check_raw_iff`
reconstructs an arbitrary raw parent code inside `Prop` with the existing
total decoder, then reuses `check_lists` at the original fuel. The shared
`decode_spec` proves both requoting and the depth bound; the two old results
are projections. No raw-input, fuel or well-formedness premise is added.
All32 executable definitions, tree data, imports and old public statements
are unchanged. The two files decrease from165/461 to131/442 lines, removing53
physical lines (54 nonblank lines), including the new invariant.

All five fresh source/olean builds, five existing focused checks and two
axiom audits returned zero; all26 existing runtime controls are true.
Malformed-input, rejection and insufficient-fuel behavior are retained.
The shared proof causes `decoded_depth_le` to inherit standard
`Classical.choice` through `Nat.pair_unpair`; its former
`[propext, Quot.sound]` set becomes the standard three. The other12 audited
old results are unchanged, including the choice-free standard axiom sets of
`check_sound` and `checkWithFuel_sound`. ROOT read the complete changed proofs
and reviewed the independent exact-final source/decoder-contract review.

## Evaluator transport, carrier wrappers and Option injectivity

ROOT applied packet e's proof-body cleanups as
`2924138249`. `ArithmeticDAG.run_map` uses its induction hypothesis on the
same appended buffer; `first_norm_facts_int` casts the whole gap disjunction;
`Carrier66` simplifies canonical zero and infers retained coordinates in the
positive drop/restore proofs. The `n`, `h` and `tau` branches remain
explicit. The three modules decrease from604 to573 lines, removing31 lines;
all arithmetic definitions, evaluators, coordinate maps, signatures and
positivity/rank assumptions remain exact.

All15 final calls returned zero: six module builds including the three
previously uncached `Carrier65`, `CarrierRankBounds` and `Carrier65Witness`
prerequisites; `ArithmeticDAGSemantics`, `ArithmeticDAGPowers` and
`Carrier66Source` clients; five existing focused checks; and the final axiom
audit. The earlier baseline audit and final evaluator reports agree; all
printed axiom sets are standard, with `canonical_zero` using only `propext`.
Controls retain invalid references, both coordinate maps and the excluded
rank-one Pell witness. ROOT read all changes and the independent final review.

ROOT then adopted the remaining packet-e parent lookup hunk as `4261a5e353`:
`Option.map_injective judgmentCode_injective` replaces the repeated Option
case split. This removes two more lines, taking `AnnotatedParents` from131
to129. The named module and `AnnotatedLine` client rebuilds, existing
`AnnotatedParents` check and axiom comparison all returned zero; the
`lookup_code_maps_iff` baseline/final report is byte-identical. No import,
definition, premise or executable checker value changes.

Together these four commits remove638 lines across six modules, from1909
to1271. The reviewed series now removes2788 net Lean lines. ROOT's ordered
header comparison confirms all145 old public headers are unchanged,
including attributed and equation-style declarations; `decode_spec` is the
sole added public declaration. The source commits and reported compiler
observations were reviewed for this documentation update; no new build or
project script was run to prepare it. Other queued proposals remain
uncertified at their separately recorded scope.

`alternate_encoding_research` independently reviewed the complete final
coefficient, decoder and three small algebra/carrier sources and their
library contracts, returning PASS on the exact final source hashes. ROOT
implemented and checked the later two-line Option cleanup separately.

ROOT also freshly rebuilt the unchanged maintained decimal equation in
`/tmp/diophantine-decimal-page-check.FRoZyK`: the one-page153046-byte PDF is
byte-identical, with no overfull/underfull diagnostics, and was visually
inspected. Its715 printed decimal digits and fourteen distinct unsubscripted
unknowns (`J,F,α,z,f,i,T,s,w,n,η,ζ,y,γ`) satisfy the latest format
request. TeX/PDF SHA256s remain
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e` /
`417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978`.
No equation edit was needed or made.

## Continuation: shared model extraction and scanner recursion

This continuation starts at `663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda`.
The model/scanner adoption rows were ahead of the actual maintained source:
both still contained duplicate proofs. They now describe checked changes.

`intake_e13` implemented the model extraction as `3814a1da29`. The unchanged
six-axiom extraction proof is public in `ObjectArithmetic` under the distinct
name `zfAxioms_of_zfc_model`. The old `ObjectMultiplication` public theorem
delegates to it, preserving all thirteen external callers and avoiding an
ambiguous shared basename. Only the two local addition references change.
There is no new model-existence, consistency or standardness premise.
The two files shrink from419 to407 lines, removing12 lines with the wrapper
included. ROOT read both full sources and the extraction contracts;
`alternate_encoding_research` independently reviewed the exact final407
lines and the sealed-ZFC/six-axiom/completeness bridge, returning PASS.

All ten final Lean calls returned zero: both module builds, three clients
(`ObjectAdditionLaws`, `ObjectMultiplicationLaws`, `ObjectNaturalExpression`),
three existing checks (`ObjectAdditionLaws`, `ObjectMultiplicationLaws`,
`ObjectAxioms`), final public audit and new-helper/wrapper audit. The five
old public axiom reports are byte-identical. The new helper, like the old
public bridge, uses only `propext` and `Quot.sound`; the wrapper equality is
`rfl`. There were no source repairs or missing-cache retries.

`v_finite_full_static` implemented the scanner extraction as `dbc6446fa7`.
Two direct `Nat.rec` facts replace twelve endpoint inductions in the four
scanners. The complete new `NatIterate` module is19 lines, imports only
`Init`, and defines no new iteration function. Both facts are axiom-free;
the four old `scan_succ` results remain axiom-free. The existing52 executable
definition bodies and69 theorem headers remain exact, including raw-state,
fuel, rejecting-zero and completed-state behavior. Including all helper and
import costs,914 lines become891, removing23 lines.

The first helper invocation failed because Lean could not infer the constant
eliminator motive in the `rec_succ` statement. Explicit motive annotations
on its two `Nat.rec` terms resolved this; the original source and diagnostic
are retained separately. All23 final commands then returned zero: eleven
fresh source/client builds, ten existing focused checks and public/helper
audits. All49 runtime controls are true, and the20 old axiom reports are
byte-identical. There were no subsequent source failures or cache gaps.
ROOT read the full helper and all four changed proof contexts;
`alternate_encoding_research` independently read all891 final source lines,
the diff and pinned recursor contracts, returning PASS on all five hashes.

## Integer unit, square-zero and norm-obstruction reuse

ROOT combined packet e's `ShortSystem` cleanup with packet q's negative-norm
reuse as `f1b8c4abc3`. Integer unit classification and commutative product
reordering replace repeated local certificates. Nonnegativity of the five
squares lets the existing additive zero law replace five separate nonlinear
deductions. Three residue obstructions specialize
`ShortEquation.strong_ne_neg_one`: the auxiliary substitutions use
`(t-2, t*h, y)` and `(I-2, I*V, V+e)`, without imposing signs on these values.
Only one lower-layer import is added. The two modules shrink from866 to826
lines, removing40; all evaluator/polynomial definitions and old signatures
remain unchanged.

All nine final Lean calls returned zero: the planned unchanged
`TotalDegreeBound` cache prerequisite, two changed modules, `ShortFrontier`,
`ShortReducedStrong` and `Carrier65` clients, the existing
`ShortEquationAxioms` / `ProposalAxioms` checks and final audit. All49 old
public axiom reports are byte-identical. No proof budget was raised or
source repair needed. `intake_e13` independently read all826 final lines,
the exact two patches and the integer/unit/nonnegative-sum contracts,
returning PASS on both final hashes.

## Shared isolated quadratic coefficient calculation

ROOT applied packet t's complete coefficient-fibre patch as `fad90f705b`.
The generic proof sits below both ordinary and selective encodings and
requires isolation only at the tested ordered-pair sum. It proves the
diagonal coefficient once and the two off-diagonal orientations once;
unselected sums may collide. Its `CommSemiring` hypothesis adds no sign,
characteristic or global-injectivity restriction. The multi-row outside
proof reuses selective vanishing while retaining the literal natural
subtraction and all three position/target bounds.

All encoding, complementary, correction, weight, support, stride and target
definitions are unchanged. The three old modules plus the complete32-line
helper shrink from413 to393 lines, removing20. All fourteen final calls
returned zero: four modules; `DegreeSeparatedCoding`, `SelectiveCertificate46`,
`SelectiveCertificate52`, `SelectiveCarry` and `MultiTargetCarry` clients;
three existing coefficient checks; and public/helper audits. The checks
retain diagonal/off-diagonal coefficients, unused collisions, overlapping
supports, signed rows, empty families and constant-only dimension. All24
old public axiom reports are byte-identical; the new helper uses the
standard three. `alternate_encoding_research` independently read all393
final lines and the full coefficient/conditional-sum/Sidon contracts,
returning PASS on all four exact hashes.

## Direct formula-semantics specifications

`intake_e13` applied packet s's `patches/specifications.patch` to all eight
modules, committed as `4ae1ff991a`. Its twenty specification proofs use the existing `Sat`, `scons`
and formula-graph equivalences directly, replacing manual existential
unpacking and reconstruction. Every formula, binder slot, coordinate shift,
conjunction order and model premise remains literal unchanged. The proofs
cover arbitrary internal naturals of arbitrary models, as before. There is
no new helper or import overhead:1691 lines become1558, removing133 lines.

All eighteen final calls returned zero on the first attempt: eight module
builds, `ObjectOmegaSemiring`, `ObjectPolynomial` and `ObjectResidualSquares`
clients, six existing checks and the final107-public-theorem axiom audit.
The six checks are `ObjectAdditionLaws`, `ObjectAdditionCancellation`,
`ObjectMultiplicationLaws`, `ObjectDistributivity`, `ObjectOmegaSemiring`
and `ObjectAxioms`. The entire107-result baseline/final audit logs are
byte-identical. There were no warnings, source retries, cache gaps or
proof-budget changes. `v_finite_full_static` independently read all1558
final source lines, the full patch/diff and actual formula/semantic contracts,
returning PASS on all eight hashes. Its review verified all120 theorem
headers and57 definition/instance regions unchanged and traced the nested
successor witnesses, expression offsets, all eight bound tags and sealing
witness shifts. ROOT read the whole patch and independently compared all
nineteen retained baseline/final zero-exit receipts and the107-result logs.

Together these five groups remove228 maintained Lean lines across21 files,
including both new helpers:4303 lines become4075. The reviewed iteration
series now removes3016 net lines. ROOT's ordered comparison verifies all420
old public headers and all158 existing data-definition bodies unchanged.
The equation artifacts retain their checked decimal format and distinct
unknown names. The iterative goal remains active.

The next-target census corrected several advertised savings before adoption:
q's single-client minimum-saturation helper adds7 whole-file lines, u's
first-failure helper saves only2, and t's first-exit alternative adds13.
At that checkpoint the w formal-polynomial `RefinedPair` proof removed chosen
complex roots but added3 lines and had no successful maintained-tree replay.
These remain possible complexity improvements, with no new validation claim.
Wang interval/periodicity refactors are deferred while the other session
is actively extending the surrounding machine and tiling construction.

## Formal polynomial identity for the two-radicand combiner

This continuation starts at `9f35798db4a63c25e435fca14d75931144657d7e`.
`v_finite_full_static` subsequently ported w's complete
`patches/refined-pair-algebraic.patch` as `57a5eed4d8`. Injectivity of
`MvPolynomial.expand 2` proves the formal `core_eq` identity before
evaluation. This replaces the two chosen complex roots and the cast argument;
`value_eq` becomes a specialization of a polynomial identity. The old value,
sign equivalence, sign-product proof and public theorem signatures remain
unchanged. The complete source grows from83 to86 lines, a three-line cost
for simpler mathematical prerequisites and the new formal theorem.

Seven final Lean calls pass on the first attempt: target, `JonesSyntax`,
`ExecutableJones` and `EquationFromRep` clients, existing `CompilerAxioms`,
old-public comparison and new-core audit. The earlier baseline audit is
separate. Both old public axiom reports are byte-identical, the new core
theorem uses the standard three, and all63 existing compiler endpoints print
only standard axioms. No dependency adjustment or elaboration repair was
needed. The direct complex-polynomial import is removed; `Complex` remains
available through transitive imports, so no global dependency-removal claim
is made. ROOT read the complete final proof and receipts. `intake_e13`
independently read all86 final lines and the full expand/evaluation contracts,
returning PASS on the exact source hash.

## Native Pell lower-ratio and odd-index reuse

`intake_e13` adopted only s's `NativePellPower` hunk as `f1949d7be7`.
The lower estimate specializes the ordinary undoubled result, multiplies
the strict natural inequality by positive two, then rewrites the original
doubled coordinate. No ratio, rank or positivity premise changes. All nine
old headers are unchanged, as is the later source-recovery argument.
Including the lower HTP import,180 lines become163, removing17 lines.

All nine final calls pass: target, `NativeBinaryScale`,
`NativePellScaleBounds` and `NativePopulationLower` clients, their four
existing focused checks including `NativePellPower`, and the nine-public
axiom audit. The complete old/new reports are byte-identical. The existing
unused-`hd` warning in `NativeBinaryScale` remains; no target proof repair or
cache gap arose. `alternate_encoding_research` independently read all163
final lines and both actual lower-estimate contracts, returning PASS.

The same author adopted k's oddness-only patch as `f3b6ad87d0`.
`SignedPellResidue.odd_index_of_base_dvd` applies to the classified first
root using exactly `I ∣ I*u`. It replaces the repeated even-index modular
contradiction. The unused positive-index intermediate is deleted; all seven
public theorem statements, sign alternatives and the `hy` premise remain.
Including the added import,230 lines become210, removing20 lines.

The first target invocation stopped before elaboration because the newly
imported, unchanged `SignedPellResidue` had no cached object. Building that
one prerequisite resolved the gap. An audit launched before the target
refresh read the old cache and is explicitly excluded from final evidence.
All ten final calls then pass: prerequisite, refreshed target,
`NativePellBootstrap`, `NativePellFirstIndex` and `NativePellPower` clients,
four existing focused checks and refreshed seven-public axiom audit.
The whole final audit equals baseline. The retained `hy` premise now emits
an unused-variable warning because its dead intermediate was removed;
neither the API premise nor linter settings were changed. The signed negative
quotient and sum-residue controls remain. ROOT read the changed proofs and
actual logs. `alternate_encoding_research` independently read all210 final
lines, the full shared residue module and underlying Pell index-congruence
contracts, returning PASS.

## Shared-register pairing projection certificates

`v_finite_full_static` reused the already imported pair-existence helpers in
the two `RegisterNatPairing` correctness fields, committed as `4fc484d4c8`.
The two natural witness slots retain the missing pair component first and
the inequality slack second. There is no new helper or import:160 lines
become148, removing12 lines. Four final calls pass on the first attempt:
target, existing `RegisterRelations` client/focused check, thirteen-public
axiom comparison and complete old-source equality audit. The earlier baseline
audit is separate, and all thirteen old axiom reports are byte-identical.

The equality audit compiles the actual immutable old source under a separate
namespace. The kernel accepts `rfl` for both complete relation records,
both graph records and `program left right` for every parameter. Thus the
whole program, wire choices, witness layout and graph expression are preserved,
including41 graph witnesses,238 operations and degree at most4. ROOT read
both full sources and the complete audit. `alternate_encoding_research`
independently read all148 final lines and the certificate/finite-witness
contracts, returning PASS. That reviewer suggested the reuse during the
census but did not author the implementation or its checks.

## Cyclic rotation and selective support from existing algebra

ROOT ported i's rotation proof as `afbec38df7`: convolution with the single
impulse at `t` is exactly rotation by `t`, and its word is the required power
of the radix. The old word/convolution theorem already proves the congruence.
No digit-size or temporal-alignment hypothesis is added, including at radix
one or length one. The module shrinks from176 to159 lines, removing17.

ROOT extended i's selective degree idea as `8274c8f6b2`. Standard bounds on
finite sums of monomials give the kernel degree directly; product/power
bounds give the row-product degree once. Coefficient vanishing then follows
from that degree theorem. The two existing public lemmas are reordered to
share this argument, preserving their statement set. Zero polynomials,
empty row families, cancellations and unused collisions remain allowed;
the actual truncated complementary exponents are unchanged. Including the
new big-operators import,194 lines become176, removing18 with no helper.

All twelve final calls pass on the first attempt: both changed modules,
four fresh clients (`NativeBooleanRotation`, `NativeCyclicCarryWord`,
`SelectiveCoefficientBounds`, `NativeQuadraticPositions`), the planned
uncached `NativeCyclicCarry` prerequisite, four existing focused sources and
the final22-public axiom comparison. The focused sources are
`NativeBooleanRotationChecks`, `NativeCyclicCarryWordAudit`,
`checks/SelectiveCarry` and `checks/NativeQuadraticPositions`. They retain
Boolean fractional/whole-phase and non-Boolean carry controls, signed packing,
rejected low blocks and the actual native top-exponent bound. All22 old
axiom reports are byte-identical; all logs are free of warnings/errors.
`intake_e13` independently read all335 final lines and the full convolution,
degree and zero-coefficient contracts, returning PASS on both final hashes.

Together the six source commits reduce1023 lines to942, removing81 net lines
after fully charging the three-line formal-identity increase. The reviewed
series now removes3097 net lines. ROOT verifies the unchanged set of65 old
public headers, allowing the intentional selective-lemma reordering. Nineteen
definition bodies remain byte-identical; the two changed proof-record fields
retain identical data fields and the complete records are kernel-equal as
described above. Equation artifacts are unchanged. The iterative goal remains
active.

## Native span frontier and shared Jones semantics

`intake_e13` adopted y's native position proof as `39a52d6353`. For rows
0–20, the target itself is at most7516, so the ordinary natural-subtraction
bound suffices for every pair. Only row21 reaches7678. Its five actual
supported entries have complementary exponents7407,7474,7411,7478 and7516;
the retained five `decide` branches check precisely these entries. The full
22-row support and coefficient data, all four ports and every old public
statement remain unchanged. The module shrinks from258 to177 lines without
an import or helper.

Seven final calls pass on the first attempt: target, `NativeQuadraticSource52`
and `NativeNinePolynomial52` clients, their three corresponding existing
focused checks and all15 old public axiom reports. The earlier baseline audit
is separate, and the complete reports are byte-identical. Existing controls
retain the attained top exponent7516, the vanishing coefficient7865 and the
source/full-polynomial transports. No cache gap, source repair or warning
occurred. `alternate_encoding_research` independently read all177 final lines,
the original diff and actual support/weight/degree contracts, returning PASS.

`v_finite_full_static` adopted ze's evaluation API patch as `80eabc57c8`.
Five already proved Jones syntax bridges become public; the executable
module reuses them at one qualified call site and deletes its five duplicate
private proofs. No new proof, import or simp attribute is added. All26 old
public statements and21 executable definition regions are unchanged. The two
modules shrink from479 to430 lines, removing49 lines.

Nine final calls pass on the first attempt: both targets, `EquationFromRep`,
`SimplifiedJones`, `CompactedJones` and `ZFCFromProgram` clients, the existing
63-endpoint compiler check, all26 old public axiom reports and the five exposed
bridge audits. The earlier baseline is separate; all old reports are
byte-identical. The radicand/weight bridges use the standard three axioms,
and divisor/dividend/margin use only `propext`. `intake_e13` independently read
all430 final lines, the complete baseline diff and actual evaluator/record
contracts, returning PASS on both unchanged final hashes. The reviewer did
not rerun compiler checks or write source.

## List-sum coefficients and arbitrary internal environments

ROOT adopted zg's coefficient patch as `ed32381986`. A private bridge identifies
the unchanged recursive interpretation with the list sum of its monomials.
Standard append, negation, multiplication and additive coefficient-map laws
replace five repeated transport inductions; equivalence injectivity supplies
the exponent equality test. List order, multiplicity, empty lists and cancelling
coefficients remain allowed. Executable expansion and coefficient extraction
are unchanged. Including the private helper and new import,120 lines become110.

ROOT adapted zg's environment restriction as `be154fa93b`. Injectivity of
`Fin.val` makes restriction of infinite environments onto finite tuples
surjective; the existing empty-set value supplies an explicit default. An
explicit guarded predicate fixes the initial candidate's motive-inference
failure. This quantifies over every internal tuple, including the zero-variable
case and nonstandard naturals, without any extra model hypothesis. Direct
`evalForm_spec` simplification also proves the unchanged equation formula's
shifted binder semantics. Formula definitions and public statements remain
unchanged;98 lines become82, removing16 lines after charging the annotation.

All nine final calls pass: both targets, `QuarticSyntax`,
`ObjectNaturalSemiring` and `ObjectEquation` clients, existing `CompilerAxioms`,
`ObjectAxioms` and `ObjectOmegaSemiring` checks, and all15 old public axiom
reports. The earlier baseline is separate; the complete old/new reports are
byte-identical. There was one initial object-target inference failure, resolved
by the explicit predicate; no dependency adjustment or further repair was
needed. `alternate_encoding_research` independently read all192 final lines,
the complete diff and actual list, polynomial, satisfaction, sealing and
restriction contracts, returning PASS on both unchanged hashes.

These four source commits reduce955 lines to799, removing156 net lines and
bringing the reviewed series from3097 to3253. ROOT compares all56 old public
headers and35 complete definition regions with immutable `f00ba53b33`; all are
unchanged. The three groups have25 successful final Lean calls and three
successful baseline audits, plus the single recorded failed initial inference.
Independent static review is additional source evidence, not another compiler
run. The iterative goal remains active.

The maintained `equation.tex` and `equation.pdf` were separately audited for
the user's notation preference: the packed integer is printed as715 base-10
digits, and the fourteen unknowns have distinct, unsubscripted names. Indexed
tile/action symbols are explicitly fixed constants. PDF extraction agrees with
the source, and a fresh `pdflatex` build reproduces the committed one-page,
153046-byte PDF exactly. Neither artifact needed an edit. Their SHA-256 hashes
remain `a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`
and `417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978`.

## Integer disequality and finite physical-order rigidity

ROOT adopted zj's signed-square proof as `91bb6ff650`. A nonzero integer
has positive square, hence square at least one; its square-minus-one is
therefore exactly a natural slack. Conversely, the supplied natural slack
forces positive square. The proof allows negative values and zero slack,
including values1 and−1, and rejects zero. Only the correctness field changes;
the one witness, expression tree and both conditional graph constructors are
unchanged. The module shrinks from68 to65 lines without a helper or import.

Six final calls pass: target, `AnnotatedCodeGraphs` and `NativeFormulaGraphs`
clients, existing `ProposalAxioms`, four-old-declaration axiom comparison and
the complete original `nonzero` record equality audit. The earlier separate
baseline is additional; all four reports are byte-identical. The kernel checks
`rfl` for the actual immutable old record, compiled under a separate namespace,
for every supplied expression. `alternate_encoding_research` independently
read all65 final lines, the full diff and actual signed-square/cast contracts,
returning PASS on the unchanged final hash.

ROOT adopted zj's finite-order proof as `52519f1cd6`. Strict monotonicity gives
an injective order homomorphism on the same finite linear order; the library's
finite-order identity theorem yields pointwise identity directly. Empty,
singleton and arbitrary finite ordinals retain the same statement. All row,
rank, Start-at-zero, coverage and enumeration data remain literal. Including
the new lower Mathlib import,180 lines become155, removing25.

The first combined baseline query stopped before elaboration because the
physical-order object was absent. ROOT then built exactly the six missing
unchanged prerequisites (`DecimalMachine215`, `WangTiles942Data`,
`WangTiles942Core`, `WangTiles942`, `WangTiles942Permutation` and
`WangTiles942PhysicalData`), the original target and the23-public baseline
audit. All pass. The refreshed target, existing `WangTiles942PhysicalOrderChecks`
and23-public final audit pass; all old reports are byte-identical. The direct
`CurrentKernelResidues2011` client also passes against the refreshed object,
in the shared common-modulus target run below. No proof repair or budget
increase was needed. `alternate_encoding_research` independently read all155
final lines and the complete actual finite-order contracts, returning PASS.

## Guarded prime-power casts and exact-order clients

`intake_e13` adopted zl's cast-fusion patch as `8772c3b3a9`. The characteristic
cast-zero and subtraction equivalences establish the iff in one rewrite
chain, retaining the explicit lower bound before natural subtraction. Zero
modulus, modulus one and exponent zero remain in the domain. All six old
statements and imports remain unchanged;80 lines become73, removing7.

The same author adapted zl's coordinate patch as `bd12ef208c`. The actual CRT
map preserves the product/lcm order calculation. Existing exact-order theorems
at level zero supply the two endpoint identities; direct rewriting transports
the block modulus, removing a private one-use helper. This reuses stronger
existing exact-order results rather than the earlier lower-level endpoint
proofs; no new assumption is supplied. The opaque large-base barrier remains.

The supplied91-line candidate failed elaboration at three dependent-`ZMod`
`simpa` steps. Its earlier static review is superseded and is not a compiler
receipt. A kernel-checked explicit-rewrite prototype guided the repair:
rewrite the indexed modulus in the local endpoint theorem, and rewrite the
whole goal modulus before applying the block order theorem. The actual final
source is96 lines, so the saving is9 after charging all five repair lines.

Baseline preparation comprised five narrowly planned unchanged generic
prerequisites, both original targets and the auxiliary-order baseline, before
capturing all19 old public axiom reports. All nine final calls pass: both changed targets,
`CurrentAuxiliaryOrder2011` and `CurrentControllerSubsets2011` clients, their
four corresponding existing focused modules and the19-public axiom comparison.
Reports are byte-identical, with no final warnings or budget changes.
`alternate_encoding_research` independently reread the repaired96-line source,
its complete final diff and actual dependent transport contracts, returning
PASS at the new hash; its complete73-line prime-power review also remains
bound to the unchanged final hash. No claim is made that the original
uncompiled candidate passed.

## One common kernel-residue certificate

`v_finite_full_static` adopted zn's common-modulus patch as `1eb5d15000`.
The same941 selector rows, protected Start and34 controls are evaluated once
modulo47·2011·120199=11360848883. The59 chunk certificates replace the old177
certificates. Existing cast homomorphisms project the common result to each
factor, using divisibility alone; no CRT converse, prime assumption or raw
residue input is introduced. Every old residue and unconditional H wrapper
remains. Both executable definitions and the entire original physical-order,
reindexing and `rawWord_cast` prefix are byte-identical. Including the new
`K_cast_common` theorem and private projection helper,843 lines become426,
removing417 lines and14157 bytes.

An initial baseline audit stopped before elaboration on the absent target
object. Baseline preparation used four additional missing unchanged controller
prerequisites and ROOT's shared physical-order chain above. The original target
and15-declaration baseline audit pass before modification. A separate unchanged
`NativeRankVariation` prerequisite was later built for the final units client.
All six final
calls pass on the first attempt: target, `CurrentControllerUnits2011` client,
their two existing focused modules,15-old-declaration comparison and the new
common-residue audit. All old reports are byte-identical; the new theorem uses
the standard three axioms. The final target run also supplies the physical-order
direct-client evidence above and is counted once in the aggregate.

The existing focused checks retain non-field semiring and empty-list cases,
Start omission and marker/scale mutation controls, independent zero exponents,
wrong literal width and `q=1` controls. The two old exponent-threshold
warnings in unchanged `CurrentMasks2011` and one in the unchanged units client
remain; no options or limits were increased. The author's five preparation,
two baseline and six final calls all pass; the early cache failure is separate.
Raw timings are descriptive, not a speedup claim for the larger modulus.
`intake_e13` independently read all426 final lines, the full original diff,
every chunk assembly and actual data/cast contracts, returning PASS at the
unchanged final hash. No additional compiler run is attributed to that review.

These five source commits reduce1276 lines to815, removing461 net lines and
bringing the reviewed series from3253 to3714. ROOT verifies all56 old public
theorem headers and13 definition headers against immutable `3299f4aa4c`;
twelve complete definition bodies are byte-identical, and the changed
correctness record is kernel-equal to its original as recorded above. All61
old declaration axiom reports are identical. The final suites have24 successful
calls when the shared residue target is counted once; unchanged prerequisite,
original-source, baseline and prototype checks remain separately described.
All final sources passed independent full review. The unrelated three-line
padding cleanup is unedited because of its larger uncached construction
closure; optional zo LTE-spectrum and Pell ports remain for later iterations.
Equation artifacts and their decimal, distinct-name presentation are unchanged.
The iterative goal remains active.

Sync merge `b36663f62c` incorporates immutable upstream `09eaa57ae5` and
retains both sides' adoption-table additions. Of159 protected source,
dependency, pin and equation files, only `AnnotatedProofChecker` changes:
upstream inlines its existing list-membership wrapper. The five simplified
modules retain their exact checked hashes, and mathlib remains unchanged and
tracked-clean. ROOT freshly rebuilds the checker and its three affected
ancestors (`AnnotatedProofCode`, `AnnotatedCodeArithmetic`, `AnnotatedCodeGraphs`),
then their four existing focused sources. All eight additional calls pass
without warnings/errors; all eight runtime controls return true. These merge
checks are separate from the24 final port checks above. Upstream's other
proof/calibration work and its validation remain separately recorded; it is
preserved and is not added to this batch's461-line count or the reviewed series.

## Constructor bounds and native binary width

ROOT adopted x's formula-code proof as `9c37c0868c`. Monotonicity of the
existing pairing/fork constructors gives the uniform lower bound44 directly:
variable atom codes are positive, and connective tags are at least3 even with
payload zero. No induction hypothesis about a subformula is needed. This is
a uniform lower bound, not a claim that variable codes attain44. All formula,
closing-program and node-count definitions remain literal. Including all five
private supporting lemmas,148 lines become129, removing19.

ROOT adopted zg's width proof as `7f35ee6786`. The natural power-minus-one
remainder identity makes divisibility force a zero exponent remainder: a
nonzero remainder would give2≤1. No separate power equality or injectivity
argument is needed. The positive-width premise stays in the API, although
the stronger proof does not use it; its existing unused-`hd` warning remains.
Natural modulo and truncated subtraction remain valid at zero as well.
No helper/import is added;105 lines become101, removing4.

All eleven final calls pass after the separate23-public-declaration baseline:
both targets, `AnnotatedClosureGraphs`, `AnnotatedBound` and
`NativePellScaleBounds` clients, their five corresponding existing focused
sources including both targets, and the23-public final audit. All reports
are byte-identical; closure/bound runtime controls return fourteen true values.
The Binary and scale calls also provide direct-client evidence for the Pell
port below, and are counted once in the aggregate. `v_finite_full_static`
independently read all230 final lines, the full diffs and actual constructor,
pairing and natural-remainder contracts, returning PASS on unchanged hashes.
No additional compiler run is attributed to that review.

## Internal division and zero-test cancellation

`v_finite_full_static` adopted the incoming proof-deltas arithmetic patch as
`5bb366fcb8`, omitting its redundant import because the provider is already
in the maintained import chain. Quotient uniqueness cancels the common product
and compares the remainder with the divisor directly. The zero-test proof
uses internal multiplication cancellation and zero-product laws. All values
remain in the model's entire internal natural semiring; no identification
with external `Nat` is introduced. All24 original theorem headers, including
private lemmas, and nine complete definition/abbreviation blocks remain literal.
There is no helper overhead;270 lines become263, removing7.

The initial target build failed on stale imported anonymous order-instance
names, including unchanged source lines. A separate diagnostic probe also
contained an unsupported command; it is not a production proof check. Fourteen
unchanged dependent modules were refreshed individually. Both immutable original
target sources were then restored, compiled and audited, before the exact
candidates were restored. The pre-refresh and coherent old reports agree, but
the rebuilt originals establish the actual coherent baseline.

All eight final calls pass: both targets, `ObjectDivModSyntax` and
`ObjectConditional` clients, existing `ObjectDivision`, `ObjectNumericWire`
and `ObjectGuardedWire` checks, and23-public final axiom audit. The coherent
old/new reports are byte-identical and use only standard axioms. Neither
candidate proof needed repair or a budget increase. `intake_e13` independently
read both full final sources, the complete diff and actual internal-semiring
contracts, returning PASS at the unchanged final hashes.

## Arbitrary-exponent LTE and a quadratic Pell comparison

`alternate_encoding_research` composed zo's LTE spectrum over the already
adopted guarded-cast proof as `25feb7f728`. The new `lift_dvd_iff` covers every
exponent, including zero via infinite multiplicity. Exact lifting becomes a
corollary, and two divisibilities determine the original exact order without
separate zero/successor cases. All six old public statements and the fused
cast bridge remain literal. Including the new helper,73 lines become68;
source bytes grow17, so this is a proof-structure reduction rather than a
byte-compression claim. The helper uses the standard three axioms.

The same author adopted zo's Pell inequality as `88ebe8f66b`. For `r ≥ 2`,
set `u = 4^r`; then `u ≥ 16` gives `4u + 2 ≤ u²`, and the original power
comparison follows by rewriting.
All nine old statements, doubled coordinate and source-recovery formulas remain
literal. No helper/import is added;163 lines become159, removing4.

Two target `lake build` calls started a broader trace refresh than needed,
including duplicate unchanged geometry work. They were stopped with actual
exit143, with no surviving owned children; they are not validation passes.
The subsequent narrow target/client calls exposed missing `SplitCertificate59`
and `WangTiles942Data` objects before elaboration. The former was restored
explicitly by this author and the latter by `intake_e13` in its shared baseline
preparation. Both narrow retries then pass without a source repair.

Seven final calls pass after the separate baseline and unchanged prerequisite
restoration: both targets, `CurrentAuxiliaryOrder2011` client, existing prime/Pell
focuses, a new three-case arbitrary-exponent/helper focus and the15-public axiom
comparison. All old reports are byte-identical, including the two choice-free
prime helpers. ROOT's already-counted Binary/scale builds and focuses provide
additional dependent-client coverage. `intake_e13` independently read all227
final lines, the full diffs and actual LTE, infinite-multiplicity cancellation,
order-divisibility and Pell contracts, returning PASS on unchanged hashes.

These five source commits reduce759 lines to720, removing39 net lines and
bringing this reviewed series from3714 to3753. The final suites have26
successful calls when shared client evidence is counted once; cache refreshes,
rebuilt originals, baselines and unsuccessful/interrupted attempts remain
separate. All61 old public declaration axiom reports are byte-identical, and
all final source groups passed independent full review. ROOT separately verifies
all49 old public theorem headers and14 complete definition blocks against
immutable `40183b4bdc`; they are unchanged. Equation artifacts
remain unchanged. Packing-rank work is still establishing its complete original
dependency baseline; it contributes no claimed saving or final validation here.
The iterative goal remains active.

## Monoid fixed-point propagation in the controller units

`v_finite_full_static` adopted zn's fixed-power proposal as `a9f8201893`.
A private lemma for an arbitrary monoid proves that a fixed point of the
power map stays fixed under all iterates, including exponent zero. Three
checked one-step literal residues then supply the existing controller
dimension theorems. The direct finite-field import is removed, although
finite-field facts can still be imported transitively. The original natural
subtraction guard, elementary positivity proof, opaque base/kernel protection,
all27 old public theorem headers and four entire definitions remain literal.
Including the helper,201 lines become196, removing5.

Five final calls pass: target, `CurrentSafeController2011` client, both
existing focused modules and31-public final audit. The baseline audit and
unchanged missing `CurrentControllerPositions2011` prerequisite are separate
successful calls. All31 old reports are byte-identical, including two
axiom-free congruence lemmas. The existing large-exponent warning remains;
no proof repair or option change was needed. Both `intake_e13` and
`alternate_encoding_research` independently read the complete final source,
diff and actual monoid/residue contracts, returning PASS at the same hash.

## Reusing source reflection and finite-update summation

`alternate_encoding_research` adopted zn's origin proposal as `fc26c5f371`.
The origin coefficient is a direct instance of `reflected_source` at zero;
the existing word support and aligned-position bounds exclude the other
branch. No separate modular subtraction calculation is needed. All original
tuple domains, nonwrapping premises and support bounds remain unchanged.
There is no helper/import overhead;118 lines become111, removing7.

The same author adapted zn's dummy-mutation proposal as `733d023d0a`.
Applying the finite-sum update lemma directly replaces a pointwise expanded
word equality. Booleanity is still proved by constructive equality cases.
The packet's `Function.forall_update_iff` shortcut would introduce the standard
three axioms into this previously axiom-free result; a separately kernel-checked
three-line constructive proof avoids that change. The actual reduction is7
lines rather than the proposed8:193 lines become186. Across both modules,
all17 old public theorem headers, the entire `dummyIncrement` definition, imports and
options remain literal. The same support, mutation and strict range guards
are retained; there is no extra helper/import cost.

Before editing, the absent original dummy object was compiled explicitly;
the unchanged origin object had been freshly compiled in the shared rank
baseline preparation. The separate18-public baseline then passed. Seven
final calls pass: both targets, `CurrentWordHighMask2011` and
`CurrentDummySafety2011` clients, both existing focused modules and the same
18-public audit. All old reports are byte-identical. Two separate successful
diagnostic controls audit the library update facts and the constructive
Boolean proof; these are not added to the final-suite count. There were no
failed attempts or source repairs in this group. `v_finite_full_static`
independently read all297 final lines, complete diffs and actual reflection,
finite-sum and update contracts, returning PASS at unchanged hashes.

These three source commits reduce512 lines to493, removing19 net lines.
Together with the preceding five commits, nine modules fall from1271 to1213,
removing58 net lines and bringing this reviewed series from3714 to3772.
The final suites have38 successful calls, counting shared client evidence
once; preparation, original-source builds, baselines and diagnostic controls
remain separate. All110 old public axiom reports are byte-identical. ROOT
freshly verifies93 old public theorem headers and19 complete definition blocks
against immutable `40183b4bdc`; they are unchanged. All final sources passed
independent full review. The maintained equation artifacts retain their exact
checked hashes, decimal constant and fourteen distinct unsubscripted unknowns.
Packing-rank simplification is still establishing its original dependency
baseline and contributes no claimed saving or final validation here.
