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

3. **`high_mask_word`** (follow-up commit) moves from `MFCurrentHighDigits2011`
   to `MFCurrentWordHighMask2011`, its only user, taking `MFNativeMaskPopulation`,
   `MFNativeRadixDigits`, `MFNativeVariableMask`, `MFNativeSourceMask` and
   `MFPaper1982Section4` off the route. Both modules compile. The namespace
   check, run with the namespaces each module declares (for example
   `MF.NativeRadixDigits`, `JSWW1976` and `Jones1982`), is clean for all 55
   modules removed by items 1–3.

Effect of items 1–2 on the PRA endpoint's import closure, on current sources: **928 → 878
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
* `NaturalExpression.graphRep` (no users) holds in `ArithmeticRepresentation`.

## Turing-machine endpoint (machine 222)

The same audit was run on
`BusyBeaver.ZFC.KEndpoint.blank_halts_iff_zfc_refutation`, the Lean statement
that the machine halts from blank iff ZFC proves ⊥. Its route is already
tight: 95 project modules (25.7k lines), and 3,604 of their 7,059 constants
are reached. Only five modules (1.5k lines) contribute nothing: `RMBisim`,
`RMDag`, `SiteCoverage`, `PowerSyntax` and `BoundedZFCConsistency.Basic`.
The register-machine bisimulation layer (`RMBisim`/`RMDag`, 832 lines) is
imported but unused by this endpoint's term. It is the largest cut available
there, inside the BusyBeaver closure whose rebuild cost is noted above. The
local oleans of `KEndpoint219`, `KEndpoint221` and the Rotation240 PA endpoint
predate their current sources, so those were not audited.

## Superseded parallel lane (outside the endpoints)

The matrix-based `Current*2011` modules form a lane parallel to the
matrix-free `MFCurrent*2011` modules the endpoints use. Twenty-one of them are
same-named twins, and the endpoints import only four data and syntax
modules from that family: `CurrentEquationSyntax2011`, `CurrentKernelData2011`,
`CurrentMaskData2011` and `CurrentHighDigitFacts2011`. The other **60 modules
(8.2k lines)**, with their `Checks`, are imported only by each other. If the
matrix-free lane is the maintained route, retiring the matrix lane would be
the largest single shortening available on the equation side. **Decision
(Vladimir, 31 October 2026): keep the matrix lane for now.** The decision may
be revisited later.

## Proof shortening in the 254 control lane (landed)

The self-contained `BusyBeaver.ZFC.ArithmeticControl*254` lane (43 modules,
imported by nothing outside it) proved each catalogue source equation
`source cN = (path, edge)` either by `rfl` over the full 6,460-entry catalogue
list or, in the three AX constructors, by a hand-written `AtRank` tree walk of
about 25 tactic lines, 84 of them in total. `ArithmeticControlSourceRank254`
now computes the rank and edge along the path (`pathRank`, `pathEdge`) and
proves once that the computation is a structural rank witness
(`atRank_of_pathEdge`, `source_of_path`). Each walk becomes
`source_of_path (by rfl) (by rfl)` at default proof limits, and the unused
`AtRank.right_count` is dropped. The `literal_target`/`cached_target`
helpers, which had been copied privately into 13 lane modules, move to
`ArithmeticControlSourceRank254` and are opened by name.

14 files, **−2,586 / +254 lines.** All 15 changed or affected modules compile,
against fresh oleans of their 33 dependencies, which had never been built
locally. The constructor files compile in 17 s each. The research audits for
`SourceRank254` and the 433/460 constructors still report only `propext` for
the source and edge facts. The lane's historical `Research/ZFC/check_*.py`
replay harnesses pin the superseded source SHA-256s, so they record the old
bytes and would need fresh pins to be replayed.

## Copied proofs

[`dup_decls`-style census](endpoint-cone/) over `BusyBeaver/ZFC` and
`DiophantineConsistency`: **195 groups of theorem blocks that are identical up
to their own name occur in more than one file, about 2,600 redundant lines.** The
largest families:

* machine-variant lanes (`Perm252`, `Prefix246`, `Prefix250`, `Rotation240`,
  `Rotation244`, `Routing245`) repeat their simulation, site, instruction and
  box lemmas (`incr_eq_write`, `decr_eq_write`, `stopped_terminal`,
  `clean_suffix`, `covered_of_allSites`, `check_inc_bound`, `stripPath_length`,
  `reverse_carry_snoc`, …), often six times each;
* `Enum222`/`Enum254`/`EnumDom`/`EnumPerm` repeat `exec_list`, `drain`,
  `cexec_append`, `step_pl` and `execAt_pack`;
* `ArithmeticDagMacrosPerm222` and `ArithmeticL2Lib254` share `pair162` and
  `loop115` (90 + 40 lines);
* the matrix `Current*2011` lane duplicates its `MFCurrent*2011` twin, for
  example `clause_convolution`, `marker_convolution` and `south_convolution`.

**Correction to that count.** Textual identity overstates what can be shared.
Each lane defines its own `incr`, `decr`, `Reg`, `program`, `table`, … and most
copied lemmas are about those lane-local definitions. They are identical text
about different constants. A lemma can be shared only if every lane-local
name it mentions is shared too: a fixpoint over all modules of the lane, which
the census tool does not compute.

**Landed: the unprotected `Prefix246`/`Prefix250` lanes.** No endpoint or
facade imports these two lanes. With the lane-wide fixpoint, the `Prefix250`
copies of definitions and lemmas that are textually identical to `Prefix246`
are deleted and re-exported (`export … (names)`), and likewise for `Prefix246`
against the protected `Perm252` lane. The aliased names stay in their
original namespaces, so every downstream reference resolves unchanged. Covered:
`Symbolic*` (`Reg`, `Branch`, `incr`, `decr`, `markedBits` and their split
lemmas), `*Simulation` (`incr_eq_write`, `decr_eq_write`, `registerBits_eq`,
…), `Instruction*` (path-length lemmas), `RuntimeInstance*`, `Prefix250Boxes`
and `SitePrefix250`. Ten files, **−287/+20 lines**. All 135 affected modules
compile serially: both lanes, the 82 `SitesPrefix246` site batches, the boot
chunks and `BinaryPrefix246`.

**Landed: `Rotation244` against the protected `Rotation240`** (same method;
none of the lane's protected modules, `ProgramRotation244` and
`SourceRotation244`, import the edited files). Six files, **−151/+12 lines**.
All 23 affected modules compile, including the ten `BootRotation244` chunks
and `BootstrapFrameRotation244`.

**Landed: `EnumDom` against `Enum222`.** Sixteen identical definitions and
lemmas (`unP`, `gate`, `tailN`, `Good` with its lemmas, the `*_ne_one`
facts) are re-exported, for −53/+2 lines. Its dependents `L2AxiomsDom`,
`L2RootDom` and `SeedDom` compile. `KEndpoint217` names none of the aliased
declarations.

**Landed: `Routing245` against `Rotation240`.** −151/+12 lines over six
files. The lane core compiles, and so do the eight dependents that name an
aliased declaration (`Routing245Invariant` and the seven
`SitesRouting245Pilot*`), plus a spot check of cut parts, a site batch and a
bisimulation chunk. The other several hundred chunk modules name none of the
aliased declarations.

Measured, not done (lines saved by the same lane-wide fixpoint):

| target | lines | cost |
| --- | ---: | --- |
| `EnumPerm`/`Enum254` → `Enum222` | 45 + 29 | K215 (peer-pinned) and Prog254 endpoint rebuilds |
| `Rotation240` → `Perm252` (both protected) | 119 | tried and reverted: the downstream reaches the PA and Diophantine endpoints (hundreds of heavy modules), and checking only the 33 modules that name an alias is not enough for an endpoint path |

Larger savings in the protected lanes need a machine-generic formulation over
`program`/`table`, not more aliasing.

## Reproducing

```powershell
cd C:\ProveIt
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake env lean Computability/DiophantineConsistency/research/endpoint-cone/ConeExact.lean
py Computability/DiophantineConsistency/research/endpoint-cone/plan_cuts.py
```

The run takes about 7 to 17 minutes and 4.4 GB, in a single Lean process.
