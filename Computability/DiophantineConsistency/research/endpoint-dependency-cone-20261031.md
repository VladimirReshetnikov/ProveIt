# Endpoint dependency cones: what the HA and PRA endpoints actually use

Date: 31 October 2026. Tools: [`endpoint-cone/`](endpoint-cone/).

## Question

The two literal endpoints

* `HACurrentEquation2011.ha_current_iff_consistency` (HA ⊢ the 14-variable
  equation has no positive zero ↔ Con(ZFC)), and
* `PRACurrentConsistencyEndpoint.pra_current_iff_consistency` (the same in
  PRA)

import a large share of the repository. Which of the imported proof
development do they need, and which import edges can be cut so that the
endpoint's route is more direct?

## Method

[`ConeExact.lean`](endpoint-cone/ConeExact.lean) loads the compiled endpoint
environment and walks `ConstantInfo.getUsedConstantsAsSet` from both endpoint
theorems through every project constant (types and proof terms, including
instances, `simp` lemmas and `decide` certificates, since all of these occur
in terms). For every project module it reports how many of its constants the
cone reaches. It also writes the exact module-to-module usage graph
(module `A` uses module `B` when some constant of `A` mentions a constant of
`B`).

Elaboration-only dependencies (tactic and macro definitions, notation,
namespaces opened by `open`) leave no trace in terms, so every proposed cut
was compiled before landing. The analysed build predates the 31 October
afternoon merges. The counts describe that build, and the landed edits were
re-planned against the current sources.

## Findings

The two endpoints together import 877 project modules (about 190k lines,
40,041 project constants). The cone reaches **17,782 constants (44%)**.
**182 modules (46.7k lines) contribute no constant at all.**

| package | modules imported | modules with no reached constant | project constants | reached |
| --- | ---: | ---: | ---: | ---: |
| `DiophantineConsistency` | 460 | 67 | 13,597 | 8,117 |
| `ZFCinPA` | 198 | 40 | 9,841 | 4,797 |
| `BusyBeaver` | 193 | 59 | 12,424 | 4,289 |
| `BoundedZFCConsistency` | 18 | 11 | 1,714 | 326 |
| `Diophantine` | 3 | 3 | 81 | 0 |
| `BoundedPAConsistency` | 3 | 2 | 286 | 93 |
| `PAHF` | 2 | 0 | 2,098 | 160 |

Largest unused blocks (lines):

* `BoundedZFCConsistency` coding, universe-truth, level-soundness and axiom
  modules: about 17k lines in 11 modules, imported through `ZFCinPA.Translation`,
  `UniformStatement`, `ConcreteFamily` and `SuccessorSources`.
* The **Parsons rule calculus**: 37 of 44 `Parsons*` modules (3.6k lines).
  The PRA endpoint reaches its result through the bound certificate and
  `PRAStrictConReverse.comparison_if_bound`, not through the Parsons rule. It
  needs only five syntactic declarations from the whole development:
  `Strict`, `Positive`, `positive_exsItr`, `strict_positive` and `partition`.
* `ZFCinPA` validator, native and staged-successor modules (16 + 5 + 2
  modules, about 4.2k lines).
* The BusyBeaver Tarski calculus (6 modules, 1.6k lines), `Enum254`/`EnumPerm`
  (1.3k), `L2Axioms254` (0.9k), `Code254*` containers/models/proof (1.1k),
  quotient models (0.6k) and `Table253`/`TablePerm252` (0.7k).
* `SplitCertificate59` and `SplitGeometry59` (1.1k lines, `maxHeartbeats
  8000000`), imported by about twenty `MFCurrent*2011` modules that use none
  of it, together with `Diophantine.Paper1976.Lemma23` and `Diophantine.Common.Pell`.

Most unused modules are not held in by a single stray import. An on-route
module also contains other declarations that use them, for example the
standard-model agreement lemmas (`*_nat`) of the BusyBeaver arithmetic
encodings, or the Parsons rule embedding in `ParsonsPositiveRule`. Following
every usage edge from on-route modules still requires 851 of the 877 modules.
So import cuts alone can remove at most 25 modules, and the rest needs
declarations moved to off-route modules.

## Landed in this change

1. **Unused imports in the Diophantine encoding modules.** 35 `MF*` modules and
   `ArithmeticLocalNormalizationCell` drop imports of `Paper1976.Lemma23`,
   `Paper1984.Masking`, `SplitCertificate59` and `MFCurrentWordHighMask2011`,
   none of which they use. Where the exact usage graph showed a project
   dependency reached only through a removed import, it is imported directly
   (`MFCurrentKernel2011` → `ArithmeticConstructionKernel`,
   `ArithmeticLocalNormalizationCell` → `MFCurrentWordPadding2011`). The
   Mathlib modules the removed imports used to bring in are imported
   explicitly, so each module's Mathlib environment is unchanged.
2. **`ParsonsPositiveSyntax`.** The five Parsons declarations that the PRA
   chain uses move to a new module with only Foundation imports. They keep
   their original namespaces and names, so every existing reference is
   unchanged. `ParsonsStrictInvariant`, `ParsonsBasePositive`,
   `ParsonsPositiveRule` and `ParsonsTheoryNormalize` import it and lose the
   moved text. The three on-route clients (`PRAISigmaOneOpenComparison`,
   `PRAISigmaOneFiniteTranslation` and `PRAPositiveMapPack`) import the
   syntax module instead of the rule calculus.

Effect on the PRA endpoint's import closure, on current sources: **928 → 878
modules, 209.9k → 203.9k lines**. The 51 modules that leave it are 41
`Parsons*` modules, `SplitCertificate59`, `SplitGeometry59`,
`DegreeSeparatedCoding`, `SelectiveQuadraticCoding`, `SidonPositions`,
`QuadraticCoding`, `QuadraticFiber`, `MFCurrentWordHighMask2011`,
`Paper1976.Lemma23` and `Common.Pell`. No declaration was deleted. The Parsons
rule development itself is untouched and still builds as before.

Validation:

* all 47 edited or directly affected modules compile, one at a time, in
  dependency order (1,722 s of Lean time). The 35 `MF*` modules, the new
  module, the four Parsons boundary modules, the three on-route clients and
  the four `PRAPositive*`/`PRANoZeroUnary` users of `Positive` were compiled
  against fresh oleans of their edited predecessors in a scratch overlay,
  leaving Lake's build state untouched.
* For every one of the 51 modules that leave the closure, no repository module
  that loses it from its own closure names its namespace, so none can depend
  on a removed declaration.
* The full endpoint rebuild under Lake is pending: the closure is stale anyway
  from the same afternoon's `ZFCinPA` and `PRAWitness*` refactors.

## Proposed next cuts (not landed: other active lanes)

Each item names the on-route module, the off-route declarations that hold the
unused block in, and what leaves the route once they move (for example into the
module of their only users).

* `ZFCinPA.Translation`, `UniformStatement`, `ConcreteFamily` and `SuccessorSources`
  use the `BoundedZFCConsistency` coded-derivation and universe-truth modules
  only outside the cone. Moving those declarations to a separate module would
  take about 17k lines off both endpoints.
* `ZFCinPA.R2Quant` (1 of 47 constants reached) holds in ten
  `Validator*254` and `R2*` modules.
* BusyBeaver: `Permutation252Frame.registerBits`/`dispatchZip` →
  `RegisterBoxes253`, `FiniteZipper` (0.7k lines);
  `Lukasiewicz.complete` → `TarskiComplete` (0.7k); `KLowerSeed.formSeed_of_fullSeed`
  → `KSeedInterface222`, `Code254GIC` (0.7k); the `*_nat` standard-model lemmas
  of `ArithmeticHistory254`, `ArithmeticRow222/254`, `ArithmeticSeedTemplates222`
  and `ArithmeticTemplates222` → `Code254History`, `Code254Proof`, `KCode222`;
  and the `*Perm222` command modules → `EnumPerm`. These edits invalidate
  large BusyBeaver endpoint closures (KSource-class rebuilds), so they should
  be scheduled with a rebuild of those closures.
* Several shared modules serve the endpoints with one or two small
  declarations, while the rest of each module belongs to another endpoint.
  The parenthesised names are the ones the endpoints reach, according to a
  syntactic cone over the `.ilean` files. A small core module per item would
  cut the edge, as `ParsonsPositiveSyntax` does for Parsons:
  `ZFCinPA.ConcreteFamily` (`wf_numChainStep`, `wf_numChainZero`; the rest is
  the PA endpoint's certificate family), `ZFCinPA.Translation` (`env1_eq`,
  `env1_shift`, `env2_eq`, `env2_shift`), `ZFCinPA.SuccessorSources` (the
  `ShiftFixed` predicate and its numeral-chain lemmas), `BusyBeaver.ZFC.Code254`
  (`P`), `KSeed222` (`SeedProp`), `Permutation252Frame` (`physOf`),
  `ArithmeticHistory254` (`foundation_div_nat`, `foundation_rem_nat`) and
  `Lukasiewicz` (the implicational calculus without `complete`).
* `MFCurrentHighDigits2011.high_mask_word` is used only by the unused
  `MFCurrentWordHighMask2011`. Moving it there takes
  `MFNativeVariableMask`/`RadixDigits`/`MaskPopulation` off the route.
* `NaturalExpression.graphRep` (no users) holds in `ArithmeticRepresentation`.

## Superseded parallel lane (outside the endpoints)

The matrix-based `Current*2011` modules form a lane parallel to the
matrix-free `MFCurrent*2011` modules the endpoints use. Twenty-one of them are
same-named twins, and the endpoints import only four data and syntax
modules from that family: `CurrentEquationSyntax2011`, `CurrentKernelData2011`,
`CurrentMaskData2011` and `CurrentHighDigitFacts2011`. The other **60 modules
(8.2k lines)**, with their `Checks`, are imported only by each other. If the
matrix-free lane is the maintained route, retiring the matrix lane would be
the largest single shortening available on the equation side. That is a
decision about which results the repository keeps, so it is left as a
proposal.

## Reproducing

```powershell
cd C:\ProveIt
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake env lean Computability/DiophantineConsistency/research/endpoint-cone/ConeExact.lean
py Computability/DiophantineConsistency/research/endpoint-cone/plan_cuts.py
```

The run takes about 7 to 17 minutes and 4.4 GB, in a single Lean process.
