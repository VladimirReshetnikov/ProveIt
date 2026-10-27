# A Diophantine equation for syntactic consistency of ZFC

Research started 23 October 2026, from repository commit `22e75dd6b8`.
This directory contains active research, its Lean proofs, and the delivered
manuscripts in [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md).
The manuscript collection was moved here from the Cardinals reports tree
on 23 October 2026 at the repository owner's request.

The target is one integer-coefficient polynomial, with an exactly stated
witness domain, whose absence of zeros is equivalent to the absence of a
finite derivation of falsity from the repository's ZFC axiom predicate.
Neither consistency nor inconsistency is assumed.

The current priority is Lean proofs that the smallest constructed equations
under the different size metrics have no solutions exactly when `Con(ZFC)`.
The owner now additionally requires a Lean theorem that this equivalence
is provable in intuitionistic Heyting Arithmetic (HA). Proving existence
of such a proof is sufficient; a literal printed proof is unnecessary.
The [HA provability plan](HA_PROVABILITY_PLAN.md) tracks that stronger target.
The [current13/178/86 tradeoff](reviews/thirteen-scaled-norm-syzygy86-root.md)
now has independent Lean and complete finite audits, preserving the entire
positive zero set and current47,313-byte coefficient tuple. It lowers the
current thirteen-variable family's degree at substantial operation cost;
historical larger-tuple forms remain separate comparisons. Its HA endpoint
is still open.
HA now [decides the interpreted strict-order atom](reviews/foundation-ha-order-decidable-root.md)
and proves its double-negation stability for arbitrary terms. Two independent
builds pass twelve reports using only propext and Quot.sound. This supplies
an atomic prerequisite for the pending bounded-checker comparison.
The [strict interval laws](reviews/ha-strict-intervals-root.md) now prove
the empty interval and the exact successor split inside HA, with twelve
independently checked propext/Quot.sound-only reports. They support the
next bounded-quantifier construction; literal checker normalization remains
a separate obligation.
The [bounded-quantifier theorem](reviews/ha-bounded-quantifiers-root.md)
now proves actual HA decisions for finite universal/existential bounds
from the explicit uniform matrix-decision formula. Its simultaneous HA
induction and two independent builds pass seventeen propext/Quot.sound-only
reports. Structural bounded syntax and the actual checker comparison
remain separate clients.
The [actual Foundation Δ₀ theorem](reviews/foundation-ha-deltazero-root.md)
now proves HA decidability of the ordinary interpretation with arbitrary
term environments. It uses actual bounded syntax and exact binder shifts,
with twelve independently checked standard-only reports. The actual delta-one checker normalization remains open.
The [bounded ordinary/GG comparison](reviews/foundation-ha-deltazero-gg-root.md)
now proves both HA implications for actual Foundation Δ₀ formulas and
arbitrary term environments. Two independent builds pass nine standard-only
reports. Existential recovery uses the whole bounded existential's actual
HA decision; the literal consistency-checker comparison remains open.
An [explicit translated ZFC consistency sentence](reviews/foundation-zfc-consistency-nat-root.md)
now has a checked standard-Nat meaning equal to the actual syntactic
ConZFC proposition, including Choice. Its independent two-leaf replay
passes eight standard-only reports. This fixes the semantic target; the
HA equivalence remains open.
For [two fixed translated consistency sentences](reviews/foundation-ha-zfc-validator-root.md),
both HA implications are now proved with no supplied source-proof premise.
The actual closed PA theorem and the checked proof map supply an HA proof.
Its independent replay passes eight standard-only reports. Connecting the
current equation and the untranslated checker is still required.
The owner reaffirmed HA after considering PA as an alternative. The
[represented C222 formula encoder](reviews/validator-formula-encoder222-root.md)
now passes an independent five-source build with13 standard-only reports,
including internal constructor and nested SHIFT equations. The complete
HA equivalence still requires the documented proof-interpretation and
runtime bridges.
The [uniform typed vacuity theorem](reviews/validator-environment-vacuity222-root.md)
then supplies actual internal C222 proof witnesses under explicit label
guards. Its IΣ2 induction and two fresh independent builds pass11
standard-only reports; general proof interpretation remains open.
The [finite Eind-context proofs](reviews/validator-eind-context222-root.md)
then add represented projections, cons laws, context vacuity and binder
discharge under IΣ1, with twelve independently checked standard-only reports.
Uniform formula transport remains a separate checkpoint.
The [finite atomic transport](reviews/validator-atomic-transport222-root.md)
now supplies actual C222 equality/membership certificates under the same
represented context, with zero and auxiliary-label collisions retained.
Two independent builds pass13 standard-only reports; uniform formula
transport under its explicit IΣ2 invariant remains the next checkpoint.
The subsequent [uniform alpha theorem](reviews/validator-environment-alpha222-root.md)
now covers arbitrary internal typed formulas in both directions under that
same represented context. Its explicit Π2/IΣ2 induction and two independent
builds pass fifteen standard-only reports. Arbitrary proof interpretation remains separate work.
The [numeric C222 substitution/opening theorem](reviews/validator-environment-substitution222-root.md)
now passes two independent builds with thirteen standard-only reports and
identical objects. Its actual Π1/IΣ1 induction retains total lookup,
repeated/zero labels and the exact qVec binder shifts. Semantic quantifier rules and the complete HA equivalence remain open.
The [actual C222 evaluation laws](reviews/arithmetic-command-evaluationperm222-peer.md)
now identify terminal with any stopped run and prove the exact head/tail
successor equations. Independent review and two fresh builds pass six
standard-only reports with identical objects. These supply the local laws
for the separately developed fair scheduler reach theorem.
The [ordinary-source construction](reviews/native-ordinary-source-construction-root.md)
now accepts every positive old-z source zero and rebuilds a Carrier65 zero
with the same scalar fields and rank. Two independent builds pass twelve
standard-only reports and identical objects. Actual current-source
existence is externally equivalent to inconsistency; shifted-z/historical
low-degree transfer and the final HA proof remain separate obligations.
The [actual C222 stream theorem](reviews/validator-environment-streams222-root.md)
now selects an explicit safe opposite-parity stream and proves relabelling
between arbitrary free-safe starts, including overlapping s/s+2. Independent
builds pass fifteen standard-only reports with identical objects. Semantic
quantifier inference and arbitrary proof interpretation remain open.
The [actual C222 fair scheduler](reviews/arithmetic-enum-fairperm222-peer.md)
now reaches every internal candidate at or above its initial counter,
including a start at4, unless an earlier command halts. Two independent
builds pass fourteen standard-only reports and identical objects. The
proof retains a bounded stopped-time witness before enumeration resumes;
compiler/proof-state invariants and exact215 calibration remain open.
The [actual raw-command replacement](reviews/arithmetic-command-replaceperm222-peer.md)
now preserves the permuted command's meaningful arguments and its complete
working-register effect over internal IOpen inputs. Independent builds
pass thirteen standard-only reports with identical objects, including raw0
and literal AX y/x order. Represented append and execution composition
remain subsequent runtime checkpoints.
The [finite actual C222 quantifier rules](reviews/validator-quantifier-rules222-root.md)
now prove ALL inference and both opened ALL/EXS body equivalences, retaining
an explicit vacuity guard for hypotheses and deriving it for a shifted
negative source hypothesis. Independent builds pass thirteen standard-only
reports with identical objects. EXS term introduction and general proof
interpretation remain open.
The [actual C222 append graph](reviews/arithmetic-command-appendperm222-peer.md)
now has all-internal IΣ1 lookup, identity/associativity and totality proofs,
plus actual finite command-list concatenation. Independent builds pass
sixteen standard-only reports with identical objects. The next runtime
checkpoint proves that evaluation of the concatenated words composes.
The [actual C222 bounded-stack certificate](reviews/arithmetic-stack-certificate222-root.md)
now retains one internal bound on actual proof witnesses for all theorem
stack entries. Its Delta1 stack predicate gives Sigma1 working-state
certification;push/pop and cached-falsity extraction are checked. Independent
three-file builds pass ten standard-only reports and identical objects,
including an explicitly rebuilt numeric tail prerequisite.

The [actual C222 command-preservation theorem](reviews/arithmetic-command-preservationperm222-root.md)
now preserves those certificates for every internal raw command and
extracts an actual value2 falsity witness from a halt. The proof retains
AX's physical y/x and old-counter arguments. Two independent fresh builds
pass eight standard-only reports and identical objects. Reverse scheduler
induction,source/215 calibration and the final HA equivalence remain open.

The [actual C222 context calculus](reviews/validator-proof-context222-root.md)
now proves rules for internally sized implication contexts,including actual
history witnesses,deduction,subsumption,source-list shifting and enumeration
independence. Two independent builds pass sixteen standard-only reports
and identical objects. The independent inventory explicitly repairs one
omitted Aesop meta-import boundary.

The [actual C222 source-negation theorem](reviews/validator-source-negation222-root.md)
now proves both actual-checker implications for represented NNF negation,
uniform over internal typed formulas and arbitrary encoder states. Explicit
Pi2/IΣ2 code induction covers all eight source constructors. Independent
builds pass sixteen standard-only reports with identical objects. Context
quantifier transport,source derivation induction and source axiom
interpretation remain open.

The [actual C222 checker/enumerator equivalence](reviews/arithmetic-enum-soundnessperm222-root.md)
now has both directions at candidate4 and empty work, with actual closed
IΣ1 and PA derivations. The reverse uses genuine Sigma1 time induction and
certified halt witnesses; the forward uses the accepted compiler/reset.
Independent builds pass twelve standard-only reports with identical
objects. Source-ZFC,exact215 and internal polynomial calibration remain
open before the final HA endpoint.

The [actual C222 refutation-execution theorem](reviews/arithmetic-proof-word-enumperm222-root.md)
now proves that an accepted internal C222 refutation forces the actual
permuted enumerator to halt from candidate4 and any working state. A real
AX reset and candidate bound discharge the scheduler premises. Independent
builds pass eight standard-only reports and identical objects. The literal
closed conditional has actual IΣ1 and PA derivations. Reverse soundness,
source/215 calibration and the final HA equivalence remain open.

The [all-internal C222 compiler](reviews/arithmetic-proof-word-perm222-root.md)
now maps every accepted internal proof code to a represented command word
with its exact conclusion and arbitrary initial top/saved stack. Genuine
Pi1 prefix induction proves correctness,with no supplied global invariant.
Its conditional false1 word halts from state(top,S,0,0). Independent builds
pass eleven standard-only reports and identical objects. The reset and
forward scheduler bridge are accepted above;reverse soundness,source
calibration and the HA equivalence remain open.

The [actual C222 compiler row](reviews/arithmetic-proof-word-rowperm222-root.md)
now has a total fixed arithmetic graph for all twelve branches and invalid
tags. Actual row acceptance and local child contracts imply its exact
all-top/all-stack execution contract. Independent builds pass six
standard-only reports and identical objects. The unrestricted rho8 choice
is fixed before Type0 models; the represented proof-history induction is accepted above.

The [uniform unrestricted rho8 circuit](reviews/arithmetic-command-rho8-circuitperm222-root.md)
now supplies one finite circuit before every internal model/input quantifier,
with no residual dominance condition. Actual guarded leaves and minor-first
MP implement the finite generic implication derivation. Independent builds
pass five standard-only reports and identical objects. This closes the
uniform finite rho8 step; proof-history compilation is accepted above,
and the full HA equivalence remains open.

The [actual C222 finite circuit graphs](reviews/arithmetic-command-circuitperm222-peer.md)
now represent every fixed numeric circuit by a parameter-free five-slot Σ1
graph and bind current word/leaf expressions exactly. Independent builds
pass nine standard-only reports and identical objects. The unrestricted
finite rho8 circuit and represented proof-history compilation are
accepted above; scheduler/source calibration remains open.

The [actual C222 GEN/MP rules](reviews/arithmetic-command-ruleperm222-root.md)
now preserve all-top/all-stack contracts, including GEN at zero/code1 and
both MP false-cache halt branches. Independent builds pass seven standard-only
reports and identical objects. The unrestricted
finite rho8 circuit is accepted above; proof-history correctness remains open.

The [actual C222 finite command leaves](reviews/arithmetic-command-leafperm222-root.md)
now construct all nine physical AX selections, exact gate/bundle outputs
and conditional false-target termination under all-top/all-stack contracts.
Independent builds pass eighteen standard-only reports with identical
objects. Direct rho8 retains u≤a; GEN/MP and represented unrestricted rho8
compilation remain subsequent obligations.

The [actual C222 finite blocks](reviews/arithmetic-command-blockperm222-root.md)
now prove exact cons execution, finite NIP popping, discard, zero-safe
counter loading and AX setup with its real old-counter arguments.
Independent builds pass eighteen standard-only reports and identical
objects. Selection/rule contracts and unrestricted rho8 compilation remain
separate.

The [actual C222 append execution theorem](reviews/arithmetic-command-compositionperm222-peer.md)
now proves exact evaluation composition over all internal words and states,
using a bounded stopped-pair invariant. Independent builds pass thirteen
standard-only reports and identical objects. Halt0 and positive completion
remain distinct. Proof compiler invariants and exact215 calibration remain
open.

The [actual C222 existential term rule](reviews/validator-existential-rules222-root.md)
now constructs the encoded term-instance implication and composes it under
arbitrary hypotheses. Independent builds pass thirteen standard-only
reports with identical objects, including fallback1 and repeated-zero
checks. General source-proof interpretation and the final HA endpoint
remain open.

The [fixed ordinary consistency semantics](reviews/foundation-ha-consistency-semantics-peer.md)
now proves actual closedness, arbitrary-premodel valuation independence and
exact standard-Nat meaning of the retained formulas. The negative formula
means precisely absence of an actual repository ZFC refutation. Independent
builds pass seven standard-only reports and identical objects. This binds
the normalized HA target semantically; the equation/source arithmetic
proof and internal checker comparison remain separate obligations.

The [ordinary predicate syntax/semantics theorem](reviews/foundation-pahf-ordinary-semantics-root.md)
now proves actual closedness and arbitrary-premodel valuation independence,
plus exact ordinary interpretation over Nat. Independent builds pass eight
standard-only reports and identical objects. The fixed consistency specialization is accepted above; the
equation/source arithmetic proof remains open.

The [fixed HA consistency normalization](reviews/foundation-ha-consistency-normalization-peer.md)
now proves both HA implications between the retained fixed GG consistency
sentence and HA negation of the ordinary actual positive ZFC-refutation
predicate. Independent builds pass eight standard-only reports and identical
objects. This does not supply the equation/source PA theorem or an internal
comparison with an independently encoded checker.

The [actual Σ1 ordinary/GG theorem](reviews/foundation-ha-sigma-one-gg-root.md)
now proves HA equivalence of the literal GG image with double negation of
the ordinary positive formula, for arbitrary environments. Independent
builds pass eleven standard-only reports and identical objects. The fixed consistency specialization is accepted above; the full
equation equivalence remains open.

The [HA finite bounded double-negation theorem](reviews/ha-bounded-double-negation-root.md)
now proves both implications for an arbitrary matrix, with no decision
premise. Independent builds pass eight propext/Quot.sound-only reports and
identical objects. Fixed consistency specialization and the full HA equation equivalence
remain open.

The [literal adaptive power recovery](reviews/native-adaptive-power-recovery-root.md)
now derives X=2^R,the exact first index2n=R+1,and the required signed
divisibility from the actual positive carrier tuple. Its projection retains
3|q and its growth uses the actual eta/zeta split. Four independent builds
pass fourteen standard-only reports and identical objects. Mersenne
factor-three exclusion,whole-product/source transfer,the converse and
internal HA arithmetic remain open.

The [literal adaptive strong-index theorem](reviews/native-adaptive-strong-index-root.md)
now recovers the actual main Pell coordinates at target R from literal
A0/A1 and Fs/Fa, preserving unrestricted positive J. It derives square
divisibility and both auxiliary congruences before index identification,
with positive actual V/y and quotient witnesses. Independent builds pass
three standard-only reports and identical objects. First-index/power
recovery, source transfer, converse and internal HA arithmetic remain open.

The [adaptive rank-window theorem](reviews/native-adaptive-rank-window-root.md)
now derives the target window, both Pell classifications, n>=25, n<p,
p>=6, a positive main ordinate, the large-c bound and both 2p<c/2R<c
bounds from the literal A0/A1 equations and stated port/positivity data.
Two independent builds pass five standard-only reports and identical
objects. Signed divisibility needs no assumed nonnegative quotient.
Strong-index restoration, power recovery, the converse and internal HA
formalization remain open.

The [adaptive main-carrier bootstrap](reviews/native-adaptive-main-bootstrap-root.md)
now derives a positive integral main Pell root and q^4 dividing the signed
index difference from literal A1 and preceding first-carrier divisibility.
Independent builds pass nine standard-only reports and identical objects.
No restored-source or rank-window premise is assumed. Index bounds, power
recovery and the full lower-degree transfer remain separate.

The [adaptive unit-factor theorem](reviews/native-adaptive-unit-factors-peer.md)
now extracts all four factor equalities from the literal signed product1.
Finite modulo4 proofs exclude negative units without assuming factor
positivity. Independent builds pass five standard-only reports and identical
objects. Binding the full historical graph and the final HA endpoint remain
separate.

The [adaptive factor-three cancellation](reviews/native-adaptive-factor-three-peer.md)
now proves q^4 divides t from q^3 dividing Y and q^5 dividing
(4Y(X+1)+3)t, for all signed integers, including q=0 and3 dividing q.
Independent builds pass four propext/Quot.sound-only reports with identical
objects. Its index-difference client is a main-Pell transfer prerequisite;
no new equation endpoint is claimed.

The [signed adaptive first-carrier theorem](reviews/native-adaptive-carrier-bootstrap-root.md)
now derives integral positive quotient witnesses and the signed Pell-root
bound directly from literal A0, before source restoration. Independent
builds pass five standard-only reports with identical objects. Main-Pell,
rank and power restoration remain open; no lower-degree endpoint is claimed.

The [shifted-z source bridge](reviews/native-shifted-source-adapter-root.md)
now proves all22 unconditional row identities and both positive existence
maps at the current ports, deriving old-z>1 from the supplied source itself.
Four independent fresh builds pass eighteen standard-only reports with
identical objects. The historical lower-degree carrier transfer remains
separate; no equation metric or HA endpoint is promoted.
The latest [canonical-data refresh](reviews/current-equation-narrow-root.md)
passes130 affected native/client builds and92 standard-only reports,
with285 authenticated unchanged reuses and five independently refreshed
data owners. Its420 selected modules preserve the actual endpoints while
allowing the exact maintained sentence to import with Foundation.
A genuine HA derivability relation is now independently checked in
[HAProofs](Lean/DiophantineConsistency/HAProofs.lean). Existing IΣ₂/PA
validator and Rotation240 consistency theorems provide reusable arithmetic
machinery; adapting it to the exact215 machine remains open. The
[source audit](research/ha-current-equation-constructive-audit-20261026.md)
also covers the owner's K215 verification pointer.
The [exact215 arithmetic run](Lean/DiophantineConsistency/ArithmeticMachineRun215.lean)
is now represented and total at every internal time in every IΣ1 model,
with exact standard-machine semantics. Its
[independent replay](reviews/arithmetic-machine215-root.md) passed all eight
machine leaves and24 standard-only axiom reports. The
[C222 calibration audit](research/ha-c222-internalization-audit.md) separates
the remaining seed-axiom and counter4 runtime bridges to the existing internal
validator theorem; run totality alone does not prove that equivalence.
The [literal permuted-command parser](reviews/arithmetic-command-wordperm222-peer.md)
now has an internal bounded graph and agrees with the actual decoder on
every raw Nat input. Its independent build passes nine standard-only
reports. Counter4 reachability and the whole runtime bridge remain open.
The separately checked [fetch](reviews/arithmetic-command-fetchperm222-peer.md)
and [one-command effect](reviews/arithmetic-command-stepperm222-root.md)
now represent the actual permuted runtime in internal arithmetic and match
all actual Nat states/raw codes. Their four independent builds pass20
standard-only reports. Full run soundness, fairness and exact215 simulation
remain open.
The [composed full enumerator step](reviews/arithmetic-enum-stepperm222-root.md)
now also has a total internal graph and exact agreement with actual
EnumPerm.enumStep on every ordinary state. Its two independent fresh
builds pass eleven standard-only reports. The program0/program1 cases
retain the actual scheduler behavior; full-run invariants remain open.
The [represented full run](reviews/arithmetic-enum-runperm222-peer.md)
now iterates that step at every internal IΣ1 time and agrees with literal
EnumPerm.run on every ordinary state/time. Two independent builds pass
thirteen standard-only reports. Individual-word draining, scheduler
fairness and proof-state invariants remain open.
The [individual-word tick](reviews/arithmetic-command-tickperm222-peer.md)
now has a proved internal decrease of the remaining word and exact
all-raw Nat one-command semantics. Its independent pair passes thirteen
standard-only reports. Halt0 and positive successful completion remain
distinct; the draining and scheduling proofs are separate steps.
The [whole-word draining theorem](reviews/arithmetic-command-runperm222-peer.md)
now proves halt or successful completion within every internal word's
numeric bound, with total represented evaluation and a closed PA totality
proof. Its independent pair passes twenty-one standard-only reports.
Execution composition, fairness and proof invariants remain open.
The [C222 equality leaf](../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorGrowG222.lean)
now translates into the actual C254 proof predicate for every internal input
in every IΣ1 model. Its [independent replay](reviews/validator-growg222-root.md)
passed seven fresh commands and ten standard-only reports. The changed seed
and runtime calibration remain open.
The literal helper-free seed now also has
[bounded arithmetic graphs](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticSeedTemplates222.lean),
with [independent replay](reviews/arithmetic-seed-templates222-root.md).
Representation of its syntax is separate from the pending seed-validity proof.
An [actual C222 Nat checker](reviews/code222-proof-root.md) is now checked
in both directions against the calculus, and the changed
[bounded row](reviews/arithmetic-row222-root.md) has exact internal graph
semantics and standard one-step parser agreement. A separate
[generic represented history](reviews/arithmetic-sequence-history-root.md)
proves unique evaluation and lookup at all internal IΣ1 indices, retaining
the explicit represented-step premise. Its
[actual C222 instantiation](reviews/arithmetic-history222-root.md) now proves
the exact recurrence and a closed IΣ1 theorem of unique Boolean evaluation.
[Agreement with the concrete Nat decoder](reviews/arithmetic-history222-nat-root.md)
now holds for every code, including malformed inputs. Internal seed validity
and exact runtime calibration remain open.
The [actual internal C222 constructor equations](reviews/arithmetic-proof-constructors222-root.md)
now give accepted-node witnesses for all twelve rule cases, preserving the
two exact seed gates and the new growG leaf. They passed independent
compilation with15 standard-only reports; seed soundness is a separate step.
The [represented CProv222 interface](reviews/validator-provability222-root.md)
now supplies actual internal rule witnesses and finite propositional logic,
with its Nat interpretation bound to the actual calculus. Seed interpretation
and exact machine calibration remain open.
The [internal C222 equality core](reviews/validator-equality-core222-root.md)
now recovers reflexivity, the helper, specialization and rho7 from growG,
and membership vacuity from the actual gated bundle. These finite internal
proof witnesses leave semantic seed validity as a separate obligation.
The [internal relational and indiscernibility proofs](reviews/validator-eind222-root.md)
now derive quantified membership transport, fixed-binder equality interpretation
and gated vacuity in the actual C222 checker. Their four independent builds
pass24 standard-only reports and preserve zero/equal labels and auxiliary
binder collisions. The [membership-container witness](reviews/validator-seed-witness222-root.md)
then supplies actual numeric proof witnesses uniformly in every IΣ1 model,
including member label0. Its two independent builds pass11 reports. This
is a weaker containment result than the native container/GIC axioms; those
axioms, arbitrary represented proof translation and runtime calibration
remain open. Independent [relational review](reviews/validator-relational-eind222-peer.md)
and [seed review](reviews/validator-seed-witness222-peer.md) found no corrections.
The [actual internal seed closure](reviews/validator-seed-closure222-root.md)
now supplies empty objects and singletons up to the fixed Eind relation
uniformly in every IΣ1 model. Its two independent builds pass14 standard-only
reports and retain numeric proof witnesses at p=0, legal zero/equal seed
labels and explicit input-binder vacuity. No self-label vacuity is assumed.
The full native container/GIC axioms, arbitrary proof interpretation and
exact runtime calibration remain open.

The [uniform C222 matrix projection](reviews/validator-seed-image222-root.md)
now retains arbitrary internal matrices, including0, without a matrix-
vacuity premise. Explicit finite congruence handles double-negation padding
at fixed roles1/3. Two independent builds pass14 standard-only reports.
Its subset-indexed coverage deliberately retains a free input label; this
is a resource for the tagged-domain interpretation, not full CP/GIC or
the pending general proof translation and runtime calibration.

The [literal arithmetic equation sentence](Lean/DiophantineConsistency/ArithmeticCurrentEquation2011.lean)
is now independently checked, with compact numerals for every fixed port
and the exact positive-domain semantics. The HA consistency-equivalence
proof remains open.
HA now also [proves double-negation stability](Lean/DiophantineConsistency/HAEquationStability2011.lean)
of that exact no-zero sentence, by a purely logical derivation. This is
an ingredient of the proof transfer; it does not prove the consistency
equivalence.
The [Foundation-to-HA syntax bridge](Lean/DiophantineConsistency/FoundationPAHFSyntax.lean)
also now has an [independent replay](reviews/foundation-pahf-syntax-root.md),
including nested-binder substitution and variable-shift checks. The actual
[intuitionistic proof-tree map](Lean/DiophantineConsistency/FoundationPAHFLogic.lean)
now also passes [independent replay](reviews/foundation-pahf-logic-root.md),
preserving all finite assumptions in `HA.Derives`. Translated arithmetic
axioms and induction remain separate work.
The first [conventional HA arithmetic proofs](Lean/DiophantineConsistency/HABasicArithmetic.lean)
now cover the six actual axioms, equality, safe closure operations and formula
induction, including genuine proofs of0+t=t and t+1=S t. Their
[independent replay](reviews/ha-basic-arithmetic-root.md) passed19 reports
using only `propext` and `Quot.sound`; full arithmetic translation remains open.
The subsequent [HA semiring proofs](reviews/ha-semiring-arithmetic-root.md)
now derive addition/multiplication associativity and commutativity, both
distributive laws and the zero/one laws using actual formula induction.
Four independently compiled leaves passed36 standard-only reports.
HA also proves the [zero-or-successor decomposition](reviews/ha-natural-cases-root.md)
and [equality decidability](reviews/ha-equality-decidable-root.md), with
capture-safe arbitrary-term instances and explicit finite contexts.
These supply arithmetic ingredients for the translation; the full HA
equivalence remains open.
The first [eight translated Foundation arithmetic axioms](reviews/foundation-ha-arithmetic-root.md)
are now discharged by actual HA proofs of their literal GG images.
Both leaves pass independent compilation and22 standard-only reports;
the remaining equality/order axioms and arbitrary induction are explicit
separate obligations.
The [whole source equality theory](reviews/foundation-ha-equality-root.md)
is now discharged too, including congruence of the interpreted order relation.
The [actual source parameter closure](reviews/foundation-ha-closure-peer.md)
also has its exact syntax identity and a checked HA proof constructor.
The [arbitrary induction image](reviews/foundation-ha-induction-root.md)
is now proved too, using actual HA formula induction and equality transport
for x+1=Sx. The [base order packet](reviews/foundation-ha-order-base-lean-peer.md)
also discharges the literal zeroLtOne and zeroLe source images. These results
retain the existing source encodings. Four more
[order images](reviews/foundation-ha-order-witnesses-root.md) now cover
addEqOfLt, addLtAdd, oneLeOfZeroLt and ltTrans, using actual HA witnesses
and preserving the double-negated order premises. The
[final order packet](reviews/foundation-ha-order-final-root.md) now proves
mulLtMul, ltIrrefl and ltTri too, using actual HA witness construction and
formula induction. All nine source order images are independently checked.
The [full PA-to-HA transfer](reviews/foundation-ha-peano-peer.md) now composes
every equality, arithmetic and unrestricted induction image into an actual
HA proof of any PA theorem's literal GG image. Both independent leaves
pass all nine reports. The source PA proof of the exact equivalence and
the consistency-predicate comparison remain open.
The [proof-transfer adapter](reviews/foundation-ha-theory-transfer-peer.md)
now composes the existing GG and finite proof maps into actual HA
derivations, provided each used source axiom image is proved in HA. Its
concrete semiring corollary discharges that premise for all eight axioms;
independent builds pass all seven reports. The complete arithmetic
instantiation is now checked in FoundationHAPeano; exact consistency-target
comparison remains separate work.
The [generic no-zero bridge](reviews/foundation-ha-nozero-root.md) now proves
both sentence implications in HA, including successor/add-one conversion
and exact quantifier counts. The [literal current instantiation](Lean/DiophantineConsistency/FoundationHACurrentNoZero2011.lean)
now proves both implications for the original fully qualified maintained
sentence. Its seven independent builds pass18 standard-only reports.
Five narrow data owners retain all40 original declaration texts and avoid
the conflicting Matrix.map imports, with every other proof body preserved.
The generic and literal comparisons supply no source PA equivalence,
consistency-predicate comparison or internal calibration.
The [exact-current transfer adapter](reviews/foundation-ha-current-transfer-root.md)
now composes a supplied source PA equivalence into both HA implications
for the maintained sentence. Two independent builds pass10 standard-only
reports. Its negative corollary targets the literal negated GG predicate;
the source PA equivalence and consistency-predicate identification remain
explicit outstanding obligations.
The [normalized14/67/106 form](research/fourteen-normalized-product106/README.md)
now also has a complete current-port graph and independently checked
external consistency equivalence. Its identity maps retain every positive
assignment. The [root replay](reviews/fourteen-normalized-product106-root.md)
uses the refreshed current data owners and passes all six reports.
The [first-norm auxiliary correction](research/thirteen-first-norm-correction92/README.md)
has two [further reductions](research/thirteen-second-first-norm-corrections/README.md):
13 positive variables with92 operations/degree90, or97/88. Independent
finite audits and two fresh Lean builds pass, retaining every positive
assignment and both actual external ConZFC endpoints. See the
[root review](reviews/thirteen-second-first-norm-corrections-root.md).
The HA equivalence is still open. The earlier correction described below
now gives13 positive variables,84 operations and exact degree92. Either
sphere equation first forces P=1, so the correction vanishes; every
positive assignment is retained in both directions. Independent fresh
Lean builds pass eight standard-only reports, and complete normal/optimized
finite audits verify the two leading cancellations and all fixed ports.
See the [root acceptance](reviews/thirteen-first-norm-correction92-root.md).
This trades nine operations for four degrees against13/75/96. Its external
ConZFC equivalence is checked; the HA endpoint remains open.

The [standard-Nat syntax semantics](reviews/foundation-pahf-nat-semantics-root.md)
now identifies the existing GG/syntax map with the original source
sentence's truth in natural numbers, retaining all binder environments.
Two independent builds pass seven standard-only reports. This is a semantic
comparison in Lean, not an HA derivation. The fixed ZFC proof-convention
comparison still needs its provider-cache audit; available old source and
author build reports are kept separate from authenticated objects.

The owner resumed formalization on 25 October 2026. The
[formalization plan](LEAN_EQUIVALENCE_PLAN.md) distinguishes the checked
older endpoints from each literal current-equation theorem and the
separate internal-ZFC obligation. The
[size-reduction record](SIZE_REDUCTION.md) preserves the constructions and
their ordinary proofs. Later references below to the Lean pause describe
their historical checkpoints; the resumed plan governs current work.

The checked Lean checkpoints now include the current arithmetic witness
maps, both complete masks, the literal K recipe and carry budget, the
actual942-tile physical permutation, and the decimal machine's consistency
endpoint. Every positive zero of the maintained polynomial now yields a
marked cyclic word in that exact942-tile table, retaining the original
arithmetic witnesses and selector bindings, with matching colors and the
exact positive temporal stride. The [current plan](LEAN_EQUIVALENCE_PLAN.md)
records fresh checks and exact premises. The actual run extraction is now
proved: every marked word gives a blank-machine halt before its vertical
period. Composing with the checked machine endpoint proves
**ConZFC implies no positive zero** for the maintained polynomial and all
three accepted13-variable forms. The [soundness receipt](reviews/current-soundness2011-lean-root.md)
binds those exact statements and fresh checks. The actual marked tile
language now has a closed external equivalence with machine halting,
hence no marked word iff ConZFC. Its construction permits independently
large widths/heights and derives unique Start in the exact quotient.
See the [native completeness receipt](reviews/wang-tiles942-native-completeness-root.md).
The reverse arithmetic/controller construction is now closed too.
[`CurrentPositiveZero2011.no_positive_zero_iff_conZFC`](Lean/DiophantineConsistency/CurrentPositiveZero2011.lean)
proves **no positive zero iff actual syntactic ConZFC** for the maintained
polynomial. Its companion theorem proves the same equivalence for all
three accepted13-variable forms at the actual current ports. Under negated
consistency it constructs one positive13-coordinate assignment solving all
three simultaneously. The [author record](reviews/current-positive-zero2011-root.md)
and [independent fresh endpoint replay](reviews/current-positive-zero2011-lean-peer.md)
record six standard-only axiom audits and the exact domain and coefficient
binding. The source-authenticated
[361-module validation](reviews/current-positive-zero2011-closure-replay.md)
has now passed at09eaa:191 fresh compilations and170 authenticated reuses.
After merging the five upstream proof changes, a separate
[15-command refresh](reviews/current-positive-zero2011-refresh-replay.md)
also passed with54 standard-only reports; unchanged intermediate objects
were explicitly reused. After the next13 upstream proof simplifications,
a [94-command refresh](reviews/ha-postmerge-refresh-20261026.md) passed
with191 standard-only reports, including the maintained and new mixed-carrier
endpoints;353 prerequisite objects and twelve unchanged intermediate clients
were explicitly reused. Further frontier equations,
size reductions and the HA proof-existence theorem remain active work.
The new [direct witness interface](Lean/DiophantineConsistency/CurrentWitnessEquivalence2011.lean)
also proves positive zero iff an actual syntactic ZFC refutation. Negating
these maps requires no double-negation elimination; this does not turn
their imported proofs into HA derivations. Its
[root replay](reviews/current-witness-equivalence2011-root.md) passed five
standard-only axiom audits and literal current-port checks.

The current [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) print the **complete decimal Carrier65 equation
in 14 positive unknowns, exact degree 150, with 65 integer-leaf binary
operations**. All 715 decimal digits are printed. Every scalar in the
polynomial front has a distinct unsubscripted name; its five factors are
P,Q,U,W,Z and its two masks are mu,omega. The complete 430-action decoder
and 942 indexed tiles fit on one Letter page at the unchanged fonts.

Decimal notation and distinct unsubscripted scalar unknowns are maintained
display requirements. Future replacements must preserve them and update
TeX and PDF together. The latest [format continuity check](reviews/current-decimal-distinct-names-2026-10-25-recheck.json)
authenticates both complete files and all 715 digits in a fresh PDF extraction.
A fresh one-page build is byte-identical, and its whole page was visually checked.
Subscripts in the fixed tile table and decoder index constant data.

The new [mixed-carrier variants](research/thirteen-lv-carrier122/README.md)
have **13 positive variables with72 operations/degree124 and74 operations/degree122**,
at all four complete CURRENT2011 ports. Explicit inverse polynomial maps
preserve their entire positive zero sets, with positivity derived from each
zero. Both consistency equivalences are externally Lean-checked; their
complete graph/degree/whole-port audits passed independent normal/optimized
[root replay](reviews/thirteen-lv-carrier122-root.md). The72/124 point
improves both metrics of the preserved
[73/126 checkpoint](research/thirteen-corrected-strong126/README.md).
The71/128 and14/65/150 points remain separate tradeoffs. The decimal display
is preserved, and HA proof-existence formalization remains open.

The further [grouped-square variant](research/thirteen-grouped-squares96/README.md)
gives **13 positive variables,77 operations and exact degree96**, at the same
complete coefficients. Its identity witness map preserves every positive zero
of the72/124 parent. Both fresh Lean leaves and the complete normal/optimized
finite audit passed [independent root review](reviews/thirteen-grouped-squares96-root.md).
The extra five operations lower degree by28; the earlier tradeoffs and displayed
equation are preserved.

The [shared-residual presentation](research/thirteen-shared-squares96/README.md)
improves this to **13 positive variables,76 operations and exact degree96**.
Sharing `f²−1` computes exactly the same polynomial over every commutative
ring, preserving all assignments and the current-port external ConZFC endpoint.
Both fresh Lean leaves and normal/optimized full finite audits passed
[independent root review](reviews/thirteen-shared-squares96-root.md).
All four complete coefficients are unchanged. The earlier77/96 packet remains
preserved; the displayed14/65/150 equation and HA target are unchanged.

The [unit-sphere equation](research/thirteen-unit-sphere96/README.md) further
reduces this to **13 positive variables,75 operations and exact degree96**.
Its equation `(PQ)²+U²+Z²−3=0` forces three integer unit squares; the actual
negative-unit exclusions recover the same entire positive zero set in both
directions. Both Lean leaves and complete normal/optimized finite audits
passed [independent root review](reviews/thirteen-unit-sphere96-root.md).
The coefficients are unchanged. This polynomial differs from its predecessor;
the positive witness maps are the identity. The decimal display is preserved.

Two [fourteen-variable nonzero-sphere forms](research/fourteen-nonzero-spheres/README.md)
now give **71 operations/degree80** and **72 operations/degree68** with the
same complete fixed coefficients. Integer descent supplies nonvanishing
of the norm factors, and the whole positive zero sets match Carrier65 by
identity. Four independent Lean leaves and full normal/optimized finite
audits pass [root review](reviews/fourteen-nonzero-spheres-root.md). They
trade an extra variable for lower degree; no global minimum or HA proof
of the final equivalence is claimed.

The [complete padding-staircase2011 candidate](candidates/one-page-padding-staircase-carrier65-2011/README.md)
uses **47,313 raw fixed-integer bytes**, 10,812 below the preceding2471
page. It fixes Start and sorts the other941 selectors by their distinct
weights. The full weight definition and floor-rank permutation are printed;
all885481 comparisons are checked. The abstract tile table is unchanged,
and the initializer remains at physical504.

The [native proof](research/padding-staircase-independent/PROOF.md) uses
consecutive padding tests before full decoding. For binary phases7..10,
483 tests bound the first483 selectors by3, forcing at most one selector
globally; other phases give that bound directly. Low-carry resets and
marker parity then fix the binary phase, and global Start-cycle arguments
exclude both residual offsets. The complete proof includes the reflected
marker collision, all916 padding tests, masks, rank, safe subsets and both
positive P66 maps. Its
[finite certificate](research/padding-staircase-independent/certificate.json)
discharges the full controller at d = 47*2011, with auxiliary prime120199.
Independent mathematical and verifier reviews and
[root acceptance](research/padding-staircase-independent/ROOT_REVIEW.md) pass.
The separate [directional terminology amendment](reviews/padding-staircase2011-directional-terminology-amendment.md)
corrects two inherited East/West slot names and verifies the actual packed
coordinates and directed helical orientation. All frozen coefficients,
copy equalities and proof artifacts remain unchanged.

The [uniform Carrier65 proof](research/carrier65-independent/PROOF.md)
applies at these exact ports. Its complete 65-row arithmetic graph,
positive witness maps and nonzero degree-150 leading form are unchanged.
The new coefficient ports define a different specialized polynomial.
The [reverse-discovery seed identity](research/reverse-discovery-decimal-seed/PROOF.md)
preserves all 430 actions while printing 715 decimal digits instead of 781.
The complete decoder includes radix-one discoveries, both prefix endpoint
domains and the necessary halt remainder.

Complete TeX is5362 bytes, extracted nonwhite PDF text2879 characters,
PDF153046 bytes and gzip integers4230 bytes. Against the preceding2471
page, raw storage saves10812 bytes and compressed storage saves28 bytes.
Printed specification length stays unchanged; PDF serialization saves
one byte. Only the cell length, clause center and spatial exponent change
in the source. Every predecessor remains available. The
[independent page review](reviews/padding-staircase-carrier65-2011-page-peer.md)
and [CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the whole source,
all four integers, every actual PDF digit, two visual inspections, fresh
byte-identical rendering and the exact preceding record.

An independent [decimal conversion checkpoint](research/decimal-seed-stage-A-run/README.md)
verifies the preceding complete781-digit integer by a full forward and reverse
conversion, including normal/optimized checks. The separately rendered
[15-variable decimal/names page](candidates/one-page-decimal-names2963-page/README.md)
passes two full source reviews and a complete independent visual/digit review.
It is preserved as an alternative while the newer14-variable equation above
remains the maintained display. All original source, output and review records
are retained; the formatting work does not replace a newer mathematical result.

The ordinary proof is now accompanied by the closed external Lean
equivalence above, composed with the actual decimal-machine/refutation
calibration. An encoded object-ZFC proof, consistency decision or global
minimum is not claimed. The one-page footer retains its earlier conservative
native-calibration status; the current checked endpoint and validation scope
are recorded here and in the formalization plan. Lean formalization remains
active. The [decimal2953](candidates/one-page-decimal-carrier65-2953/equation.pdf),
[block-mask2963](candidates/one-page-block-mask2963/equation.pdf),
[low-padding2963](candidates/one-page-low-padding2963/equation.pdf),
[single-clause2999](candidates/one-page-parity-clause2999/equation.pdf),
[admissible942](candidates/one-page-admissible942/equation.pdf),
[Boolean4027](candidates/one-page-boolean-dummy4027/equation.pdf),
[shared-copy4049](candidates/one-page-merged-copy4049/equation.pdf),
[Start-marker4127](candidates/one-page-start-marker4127/equation.pdf),
[Start-marker4177](candidates/one-page-start-marker4177/equation.pdf),
[zero-weight6007](candidates/one-page-zero-weight6007/equation.pdf),
[one-anchor7309](candidates/one-page-one-anchor7309/equation.pdf),
[two-anchor7691](candidates/one-page-two-anchor7691/equation.pdf),
[three-anchor47](candidates/one-page-complemented47-independent/equation.pdf)
and [radix55](candidates/one-page-compact66-radix55/equation.pdf) pages remain
preserved. Reviewed [single-clause3037](research/single-clause-independent/README.md)
and [composite2983](research/composite-length-independent/README.md) proofs
are intermediate checkpoints, as is the reviewed
[scaled2953 P66 page](candidates/one-page-scaled-clause2953/equation.pdf).
The [tail-envelope bound](research/sorted-selectors-probe/TAIL_ENVELOPE_BOUND.md)
proves optimality only within its fixed full-suffix reset/controller family.
Further work tests sharper phase-dependent carry bounds and arithmetic
tradeoffs while preserving decimal notation and distinct scalar names.
The [weighted-only Psi identity](research/weighted-only-psi/NOTE.md)
preserves its bound tuple; [radix obstructions](research/radix-parity-independent/README.md)
explain why direct46/45 substitutions need different proof interfaces.

The [tile-biased single-clause family](research/tile-biased-single-clause-family/README.md)
has two full independent ordinary reviews and
[conditional root acceptance](reviews/tile-biased-family-composite2033-ROOT-conditional-acceptance.json).
Fixed corrections to the third and fourth tile components permit count
recovery before phase recovery, with a single clause at 1006 and a last
product at 2011. The [49-bit, length-2033 controller note](research/tile-biased49-composite2033-controller/README.md)
proves whole-modulus order 954, including the repeated factor in
49*2033 = 7^2*19*107. The subsequent
[five-run finite check](research/tile-biased49-2033-first-run/README.md)
finds H=0 modulo19 for the actual new kernel. No auxiliary prime repairs
that fixed-unit failure, so the2033 controller is rejected and its draft
page is preserved without promotion. The same whole conditional family
has a reviewed [Carrier65 corollary](research/tile-biased-carrier65-corollary/README.md),
retaining14 positive inputs,65 operations and degree150. The
[short-length obstructions](research/tile-biased49-short-length-obstructions/README.md)
now have [two full reviews and scoped root acceptance](reviews/tile-biased49-short-length-ROOT-two-peer-acceptance.json).
The length2039 packet remains unexecuted under CODE_ONLY/HOLD; no successful
tuple or measured equation saving is claimed. The maintained decimal page
is the padding-staircase2011 version above.

The [previous radix67 compact page](candidates/one-page-compact66/equation.pdf),
[grouped66 page](candidates/one-page-grouped66/equation.pdf) and
[original66/157 page](candidates/one-page-fifteen66/equation.pdf) remain
unchanged. Against the preserved
[ten-positive85/328 page](candidates/one-page-doubled85/equation.pdf),
the arithmetic improvement saves twenty operations and178 degree
while adding four unknowns. All predecessor pages and histories remain
available. No global minimum, consistency decision or new Lean derivation
is claimed; Lean remains paused.

The complete [unshifted-T equations](research/ten-positive-unshift-t-finite/RESULTS.md)
now reach **84 operations at degree328**, or83/436,80/750 and81/560, in the
same ten-positive domain. Each saves one addition at unchanged degree from
its whole parent. Full ordinary proofs, literal graphs, leading forms and
coefficient bindings pass separate review; four fresh root check/rebuild
runs reproduce all author records byte for byte. See the
[root acceptance](reviews/ten-positive-unshift-t-finite-root-peer.md).
Its complete85/328 ten-variable page remains available beside the new66/157 display.
The preceding [81/750 and82/560 graphs](research/ten-positive-qcube-doubled-finite/RESULTS.md)
and all complete pages remain preserved.

A separately reviewed [89-operation comparison page](candidates/one-page-uncentered89/equation.pdf),
with its complete [standalone TeX](candidates/one-page-uncentered89/equation.tex),
has the same ten-positive domain and exact degree 288. Against the preserved 92/283 page it saves three
operations with five additional degrees. All constants still fit on one
Letter page in 9-point type; the [root review](reviews/one-page-uncentered89-root-peer.md)
binds every actual printed formula, constant and coefficient to the accepted
whole source. The preserved 92/283 page remains a lower-degree comparison.
The [direct-carrier sharing extension](research/saturated-direct-carrier-cse/README.md)
also saves one multiplication in each of five complete direct variants,
including96/258,97/254 and94/262; their entire polynomials are preserved.

The [q-cube-normalized ten-positive form](research/ten-positive-qcube-normalization/README.md)
now uses 86 operations at exact degree 466. Its complete positive-domain proof,
whole native bindings and independent checks pass; this cost/degree alternative
is preserved separately. The accepted 84/436 and 85/328 forms improve both
its cost and degree. Its complete
[one-page PDF](candidates/one-page-qcube86/equation.pdf) and
[standalone TeX](candidates/one-page-qcube86/equation.tex) now pass independent
actual-formula and rendered-page checks; see the
[root review](reviews/one-page-qcube86-root-peer.md).

A complete [nine-positive comparison page](candidates/one-page-shared-odd9/equation.pdf)
and its [standalone TeX](candidates/one-page-shared-odd9/equation.tex) now fit
every constant on one Letter page at 9-point mathematics. The accepted
413-operation evaluator has exact degree 1,316,546 and uses the entire
original 722-character compact54 recipe. All actual-TeX/PDF checks, both
visual reviews and four byte-exact root replays pass; see the
[root acceptance](reviews/one-page-shared-odd9-root-peer.md). The complete
[433-operation predecessor](candidates/one-page-saturated9/equation.pdf)
and its TeX remain preserved. The new page saves 20 operations and 312,222 degrees
over that predecessor. Its lower
variable count carries substantially higher cost and degree, so the
maintained66/157 page gives a different arithmetic/variable tradeoff.

Fresh [square-radix projections](research/round16-square-weighted-projections/RESULTS.md)
give degree-four equations with315 unrestricted integer unknowns/217 rows/
7999 terms and316/218/7987, both at height14250071. Five first-attempt
commands and four fresh root replays pass byte for byte; see the
[root acceptance](reviews/round16-square-weighted-projections-root-peer.md).
These raw parents remain preserved. A separately completed
[fixed58-shift verification](research/fast-sparse-substitution-replay-verification/README.md)
now accepts weighted315/217/5743 and plain316/218/5737 at height128446
and row height256, with every coordinate live. All four first/fresh
normal/optimized processes pass and reproduce whole original reports;
all eight fresh files are byte-identical and150 inputs remain unchanged.
See the [ROOT acceptance](reviews/fast-sparse-substitution-replay-root-peer.md).
The earlier optimized exit143 remains preserved and unresolved; the old
observed source is unchanged. No fresh native or Lean replay is claimed.

A complete [balanced-shear verification](research/balanced-crt-gate-shear-verification/README.md)
now lowers the same profiles' height to98336, with weighted315/217/5809
and plain316/218/5803. The determinant-one chart preserves both whole zero
sets; all nine first/fresh processes pass and all twelve fresh capture
files match byte for byte. See the
[ROOT acceptance](reviews/balanced-crt-gate-shear-verification-root-peer.md).
The66 extra terms buy lower height; the centered parents remain smaller
in support. Height98336 is an exact minimum in this specified two-parameter
shear family followed by constant translations, with no global claim.
This quartic tradeoff leaves the maintained compact66 page unchanged.

The complete [neighbor-shear successor](research/neighbor-gate-shear-verification/README.md)
now improves those profiles to **plain316/218/5781 and weighted315/217/5787**,
both at height93109 and row height160. It removes22 terms without any
new monomial or coefficient growth. All nine actual first/fresh processes
pass, with92 negative/12 valid controls and12 byte-exact fresh capture
files;294 source inputs remain unchanged. The [ROOT acceptance](reviews/neighbor-gate-shear-verification-root-peer.md)
follows full independent evidence review and retains every composed source
map and calibration boundary. Earlier quartics remain available; this
degree-four improvement does not shorten the maintained one-page formula.

Two preceding complete integer shears reached
**plain316/218/5626 and weighted315/217/5632**, both at exact degree4,
height32053 and residual height96. The [pair-sum evidence](research/pair-sum-gate-shear-verification/README.md)
passes both full ordinary reviews and [ROOT acceptance](reviews/pair-sum-gate-shear-verification-root-peer.md).
Its nine actual first/fresh processes pass, all12 fresh captures reproduce
their first bytes, and all460 source inputs remain unchanged. Complete
saved forward/inverse/SOS identities,128 negative/12 valid controls and
all noncommuting source-restoration maps are retained. The final shear
removes114 terms and introduces12, net102 against the Pell-output parent;
this is an accepted quartic tradeoff, with no global minimum claim.

The original [second pair-sum shear](research/second-pair-sum-gate-shear/README.md)
received both full ordinary reviews and [joint bound acceptance](reviews/second-pair-sum-gate-shear-ordinary-acceptance.json),
but its first normal checker subsequently caught a row30 linear-term error
missed by those reviews and both full statics. The sequence stopped after
materialization; [all original evidence is preserved](research/second-pair-sum-gate-shear-first-failure/README.md).
The correct substitution gives−48c rather than−24c. Generated metrics
from that stopped namespace remain provisional; it has no accepted endpoint
and has not been retried. Correction required a separate bounded repair and
complete final reviews.

The separately corrected [whole R1 evidence packet](research/second-pair-sum-gate-shear-r1-verification/README.md)
now supplies the accepted coefficient-height frontier in this315/316-variable
lineage: **plain316/218/5614 and weighted315/217/5620** variables/rows/terms,
both at exact degree4, height15109 and residual height72, with every
coordinate live. Its [sealed manifest](research/second-pair-sum-gate-shear-r1-verification/MANIFEST.json),
[ROOT full ordinary review](reviews/second-pair-sum-gate-shear-r1-verification-ordinary-root.md),
[independent full ordinary review](reviews/second-pair-sum-gate-shear-r1-verification-ordinary-peer.md)
and [separate ROOT endpoint acceptance](reviews/second-pair-sum-gate-shear-r1-finite-endpoint-acceptance.json)
bind the complete corrected equation and maps. Relative to accepted U,
height falls32053 to15109 and row height96 to72. Each expanded support
loses12 terms (66 removed,54 introduced); the separate residual-monomial
occurrence saving is eight. All nine actual first/fresh processes exit0,
all12 fresh capture files match first bytes, and each of four checkers
retains172 negative/12 valid controls, including146 actual artifact and26
source-premise negatives and the wrong−24 regression in both profiles.
The accepted U parents and entire original failure history remain preserved.
No global minimum, fresh native/Lean replay or printed-page gain is claimed;
the maintained radix55 PDF/TeX and Lean pause are unchanged.

A [bounded65-bit modular probe](research/compact66-radix65-unit-probe-verification/README.md)
now discharges the three previously unknown controller-bracket unit
conditions: H0 residues5,62,418969 at primes13,8807,581197, respectively.
Both complete coefficient/modular routes and four first/fresh processes
pass, with six byte-exact fresh files. See the
[ROOT bounded acceptance](reviews/compact66-radix65-unit-probe-verification-root-peer.md).
The complete [coherent65-bit native/source adapter](research/compact66-radix65-native-adapter/README.md)
now passes both full final ordinary reviews after a separately authorized
padding-exponent naming repair; the initial source and both first findings
remain preserved. See the [joint ordinary acceptance](reviews/compact66-radix65-native-adapter-ordinary-acceptance.json).
Fresh coherent tuple verification remains separate; no numerical65-bit
endpoint or page improvement is accepted yet.

A [conditional57/59-bit proposal](research/compact66-radix57-59-padding/README.md)
also passes both complete ordinary reviews. It proves shorter whole padding
identities and, at57 bits, a sharper carry bound and an automatic rank class
modulo3. Its three new bracket-unit conditions remain uncomputed;59 also
needs a new prime/lift certificate. See the [conditional acceptance](reviews/compact66-radix57-59-padding-ordinary-acceptance.json).
Those conditional57/59-bit proposals remain separate from the verified55-bit
page; they do not supply a numerical57/59-bit endpoint or a further page gain.

The [conditional53-bit adapter](research/compact66-radix53-carry-tolerance/README.md)
also passes both full ordinary reviews and [conditional acceptance](reviews/compact66-radix53-carry-tolerance-ordinary-acceptance.json).
Its soundness proof permits bounded cyclic carries, then recovers ordinary
one-hot decoding and alignment. The [complete bounded certificate evidence](research/compact66-radix53-certificate-probe-verification/README.md)
now supplies prime2518517, the exact order/lift certificate and all three
controller units, after four actual successful runs and two FULL ordinary
reviews. [Separate ROOT acceptance](reviews/compact66-radix53-certificate-probe-bounded-acceptance.json)
discharges precisely those finite conditions. The coherent53-bit tuple and
[closed page evidence](research/compact66-radix53-page-verification/README.md)
now retain all16 actual exit0 processes,18 byte-exact fresh captures and
two actual visual PASS reviews, in77 payloads/78 whole files. The
[ROOT](reviews/compact66-radix53-page-verification-ordinary-root.md) and
[independent](reviews/compact66-radix53-page-verification-ordinary-peer.md)
FULL final ordinary reviews pass. [Separate ROOT acceptance](reviews/compact66-radix53-page-finite-endpoint-acceptance.json)
records this verified checkpoint without promoting it. Raw coefficient bytes are233666 versus242484 maintained,
but PDF nonwhite characters are2770 versus2764 and TeX bytes5207 versus5195.
This is smaller raw storage, not a shorter page; the55-bit page stays current.

The [conditional51-bit local-reset adapter](research/compact66-radix51-local-resets/README.md)
now has two FULL ordinary reviews, [ROOT](reviews/compact66-radix51-local-resets-ordinary-root.md)
and [independent peer](reviews/compact66-radix51-local-resets-ordinary-peer.md),
and [separate conditional acceptance](reviews/compact66-radix51-local-resets-ordinary-acceptance.json).
Local carry resets replace global aligned no-carry. The new lambda/lift
certificate and all three Hctrl unit values at17,L=8807,lambda remain
UNKNOWN; no numerical51 endpoint or page gain is accepted.

The [conditional49 shared-marker encoding](research/compact66-shared-marker-radix49/README.md)
passes both FULL ordinary reviews and [separate conditional acceptance](reviews/compact66-shared-marker-radix49-ordinary-acceptance.json).
All seven physical markers share clause weight2^44 and are individually
recovered. Its [closed bounded certificate evidence](research/compact66-shared-marker-radix49-certificate-probe-verification/README.md)
now passes both FULL ordinary final reviews and [separate ROOT finite acceptance](reviews/compact66-shared-marker-radix49-finite-controller-acceptance.json).
All four first/fresh normal/optimized applications exit0 with38 negative/four
valid controls each, and all six fresh capture files equal first bytes.
The first candidate lambda434011 has exact B-order18870, valuation-one lift
and bracket units2/3135/6522 at7/8807/lambda. This discharges the base49 finite
conditions and those of low-bit-padding R1, whose beta/K/controller context is
identical. No whole49 tuple, specialized source or page endpoint is yet accepted.

The [low-bit-padding R1](research/compact66-radix49-low-bit-padding-r1/README.md)
now passes two FULL nonauthor ordinary reviews and [separate conditional acceptance](reviews/compact66-radix49-low-bit-padding-r1-ordinary-acceptance.json).
It moves39 mask bits inside the proved whole zero field7693, simplifying
the telescoped MF coefficient. K and the finite controller conditions are
unchanged, but the actual rank and private witnesses are reconstructed fresh.
The [original calibration finding](reviews/compact66-radix49-low-bit-padding-ordinary-peer.md)
is preserved; R1 explicitly has five actual factors1 and Ns=Delta.

An [optional kernel repair](research/compact66-shared-marker-radix49-kernel-units/README.md)
passes both FULL ordinary reviews, with the [preserved ROOT correction](reviews/compact66-shared-marker-radix49-kernel-units-ordinary-root-correction.md),
and [separate conditional acceptance](reviews/compact66-shared-marker-radix49-kernel-units-ordinary-acceptance.json).
Its fixed choice among three harmless terms proves both fixed bracket
units symbolically. It is a longer fallback; its lambda conditions remain
open, and it is separate from the successful base49 probe.

The new [complete three-anchor47 proposal](research/compact66-three-anchor-radix47/README.md)
removes four physical occupancy markers by giving every genuine edge a positive
label and reserving zero for empty cells. Its11-bit count guard permits a
184-to22 cyclic-carry proof, including occupied raw rho+1, actual digit1 and
outgoing1 cleared by explicit resets. It retains15 positive unknowns and the
uniform66-operation degree157 front, with982 physical positions and870 padding
bits. The FULL [first](reviews/compact66-three-anchor-radix47-ordinary-peer.md)
and [second](reviews/compact66-three-anchor-radix47-ordinary-second-peer.md)
independent nonauthor reviews pass, with [separate ROOT conditional acceptance](reviews/compact66-three-anchor-radix47-ordinary-acceptance.json).
All new bracket values and admissible-prime existence remain UNKNOWN. The
unsealed prospective probe is preserved as a draft; no application or page-size
claim follows. This encoding changes the earlier scoped47 alias's ten-bit guard
and seven-marker layout.

The [complete complemented-three-anchor47 proof](research/compact66-complemented-three-anchor-radix47/README.md)
combines positive complemented labels with four-marker deletion and ten-bit
selector spacing. Its whole29-to11 carry proof covers every47 phase, all17
copies and872 LOW26 padding tests; an occupied clause has raw2^46+1<rho.
The [first](reviews/compact66-complemented-three-anchor-radix47-ordinary-peer.md)
and [second](reviews/compact66-complemented-three-anchor-radix47-ordinary-second-peer.md)
FULL nonauthor reviews pass, followed by [separate ROOT conditional acceptance](reviews/compact66-complemented-three-anchor-radix47-ordinary-acceptance.json).
The later [independent controller certificate](research/complemented47-controller-independent/README.md)
discharges the THREE-anchor conditions for its exact tuple. Its complete
[page](candidates/one-page-complemented47-independent/README.md) is retained
as a predecessor of the accepted two-anchor7691 and one-anchor7309
pages; the current display is identified at the top of this document.

The separate frozen [CODE ONLY probe](research/compact66-complemented-three-anchor-radix47-controller-probe/README.md)
never ran: upstream retired its required live ZIP after ROOT's first full
static. Its [first independent finding and ROOT disposition](reviews/compact66-complemented-three-anchor47-probe-retirement-root-disposition.json)
remain preserved. The [historical/placed association](reviews/common-remainders47-retired-archive-provenance-association.json)
authenticates the original archive and four current plaintexts. The separate
[three-anchor CODE/TEX draft](candidates/one-page-compact66-complemented47/README.md)
and its unrendered source remain historical preparation, without relabeling
any failure or importing the later independent numerical results.

The separate [two-weighted-anchor/L8191 proof](research/compact66-complemented-two-anchor-radix47-mersenne8191/README.md)
now has TWO complete independent nonauthor reviews and [ROOT conditional
ordinary acceptance](reviews/compact66-complemented-two-anchor-radix47-mersenne8191-ordinary-acceptance.json).
Its own H2 residues and controller-prime conditions remain UNKNOWN. The new
bounded probe and CODE/TEX draft were never executed; they are superseded
for immediate page work by the independently constructed L7691 tuple
and its accepted7309,6007 and4177 successors; the current display is described above. No finite certificate
transfers between these distinct specializations.
The earlier +1/spacing11 tuple likewise retains its distinct open conditions.

The [seven-archive intake](research/incoming-7a8da41437-codefree-intake/README.md)
retains reported/unverified quartic and ten-variable metrics. Those archives
are now placed as sources149--155; their original Git associations persist.
The separate [early two-anchor/composite6445 proof](research/compact66-complemented-two-anchor-radix47-block6445/README.md)
has two FULL independent nonauthor reviews and [conditional ROOT acceptance](reviews/compact66-two-anchor47-block6445-ordinary-acceptance.json).
Its new units and controller prime remain unknown. The later verified4177
construction superseded it before any new probe files or runtime captures
were created; the [disposition](reviews/compact66-block6445-superseded-root-disposition.json)
preserves that distinction. Its frozen sources, first reviews and conditional
theorem remain research history.

The [literal direct-C222 research](research/direct-c222-one-page-template/README.md)
prints every constructor, eighteen power requests and their full polynomial
certificate without a machine seed, hidden coefficient table or finite
controller premise. All three complete families now have TWO FULL independent
nonauthor reviews and [separate ROOT ordinary acceptance](reviews/direct-c222-three-families-ordinary-acceptance.json),
within their explicit standard Pell-index and C222/ZF/ZFC foundations:

| Printed family | Natural unknowns (or uniformly translated positive unknowns) | Squared residuals | Exact total degree |
| --- | ---: | ---: | ---: |
| [Original27](research/direct-c222-one-page-template/README.md) | 554 | 332 | 2097684 |
| [Successor20](research/direct-c222-twenty-power-template/README.md) | 428 | 206 | 4194312 |
| [Successor21](research/direct-c222-twenty-one-power-template/README.md) | 446 | 224 | 2097684 |

The successor maps preserve every coordinate of each full zero in both
directions. Retaining the independent Y coordinate avoids the degree increase
of the smaller20-coordinate power graph. These are ordinary hand degree
proofs; expanded support, height and operation counts remain unmeasured.
The [complete446-variable equation](candidates/one-page-direct-c222-446/README.md)
has an actual one-page [PDF](candidates/one-page-direct-c222-446/equation.pdf)
and [TeX](candidates/one-page-direct-c222-446/equation.tex), with every coefficient
defined and no packed machine seed. Its formula-preserving layout repair passed
two full independent statics; ROOT and the [independent reviewer](reviews/direct-c222-twenty-one-fit-v2-visual-second-peer.md)
opened the whole successful page and found no overlap or clipping. The original
failed fit and all nineteen successful outputs remain preserved. The
[original554-variable plan](research/direct-c222-one-page-template-page-plan/equation.tex)
is still available. This446-variable/degree2097684 equation is a separate
tradeoff alongside the maintained14-positive/65-operation/degree150 display.
Lean stays paused; substantial checked improvements update the maintained
PDF and TeX together.

The [normalized strong-factor equation](research/compact67-normalized-strong-degree145/README.md)
has two full independent ordinary reviews and [separate ROOT acceptance](reviews/compact67-normalized-strong-degree145-ordinary-acceptance.json).
It retains15 positive unknowns and lowers the exact degree from157 to145,
using67 integer operations rather than66. The identity `P157=Delta*Q145`,
with `Delta>0` before any equation, gives identical whole positive zero sets
at the pinned4177 coefficient tuple. The disclosed older normalization gains
no new variable or printed-page saving; it remains a degree/circuit tradeoff.
The maintained942-tile page is unchanged by this separate acceptance.

The [eight newest archive intake](research/incoming-3ecd6a6cf5-codefree-intake/README.md)
and [FULL incoming structural review](reviews/incoming-common-remainders-radix47-ordinary-peer.md)
keep incoming numeric certificates and page claims unverified. Reported75/626
ten-positive circuits and smaller direct quartics also merit full review.

The [exact47 layout identities](research/compact66-three-anchor-radix47-layout-identities/README.md)
also give a geometric low-mask recipe and one common selector bias, preserving
all four integers pointwise. Their printed gain remains unmeasured. The
[scale-one unshifted quotient proposal](research/compact134-scale-one-unshifted-quotient/README.md)
proves inverse positive-zero maps for incoming134 and prospective ten-positive
77/630 and78/468 layouts. Its whole67 tuple remains separate; no new finite
materialization, independent endpoint acceptance or main promotion is claimed.

The [read-only intake of incoming134–139](research/incoming134-139-codefree-intake/README.md)
prioritizes134's reported ten-positive78/630 and79/468 circuits and135's
282/287/309-integer quartic family for full review. Their domains, heights,
fixed-port costs and prior-art comparisons differ. No incoming program ran,
metric was independently recomputed, or maintained-page change was accepted.

The [scoped47 clause alias](research/compact66-shared-marker-radix47-clause-alias/README.md)
passes both FULL reviews and [separate scoped acceptance](reviews/compact66-shared-marker-radix47-clause-alias-ordinary-acceptance.json).
Its generic931..943-selector alias passes the isolated clause test with
bounded carries, including a Start-selected/Forbidden-absent931..942
subfamily. It supplies neither an actual native/P66 solution nor47 impossibility.

A lower-row direct degree-four comparison, the [complete fused-nine form](research/signed-pell-cap-nine-factor-projections/data/centered/equation.json)
now reaches **327 unrestricted integer unknowns**, with216 rows,5,718 terms
and height128,446. It saves32 variables, six rows and340 terms against the
preserved [359-variable shared-cap form](research/signed-pell-cap-projections/data/centered/equation.json).
Its ordinary source theorem, complete Horn/projection inverses, independent
normal/optimized coefficient checks and byte-exact rebuilds pass; all eight
fresh root records match the author byte for byte. See the
[root acceptance](reviews/signed-pell-cap-nine-factor-projections-root-peer.md).
The preceding329-variable refined-product form remains preserved.
The [complete grouped alternative](research/signed-pell-cap-grouped-quartic/data/equation.json)
uses364 variables,227 rows and4,574 terms at the same heights. Its unique
five-sum extension preserves every old coordinate and passes four fresh root
checks/rebuilds; see the [root acceptance](reviews/signed-pell-cap-grouped-quartic-root-peer.md).
Against the359cap chart it saves1,484 terms while adding five variables. The earlier
[433-variable helper form](research/round15-helper-guard-projections/full-data/joint_helper/centered/equation.json),
the436/439 intermediates,
[442-variable parent](con-zfc-diophantine-forms/125-unified-binomial-round15/direct/integer442/)
and all inverse certificates remain preserved. Its six natural-domain
alternatives reach329 nonnegative unknowns. The
[preceding496-variable family](research/round14-pair-guard-projections/README.md)
and all lower-height alternatives remain preserved.
The [eight-bundle intake](research/intake-5f3379063d/README.md) records the newer
319-natural,261-natural and height-one proposals with their exact review scopes.
The [seven newest archives](research/intake-fd3e384e92/README.md) add staged
84/436 and 85/328 compact leads and a 324-variable quartic proposal. Their
review qualifications and pending finite/source work are recorded separately.

The preceding [ten-positive degree408 page](candidates/one-page-quadratic10/equation.pdf)
is preserved with its [TeX](candidates/one-page-quadratic10/equation.tex),
as are the earlier [degree816 page](candidates/one-page-scaled10/equation.pdf)
and [thirteen-positive degree51 page](candidates/one-page-ordinary13/equation.pdf)
with their standalone sources. Against the older ten-positive degree408
page, the13-positive page uses fewer operations and lower degree with
three more unknowns; it remains a separate tradeoff.

The previous [fifteen-positive page](candidates/one-page-compression/merged-mask-base62/equation.pdf)
and its other notation variants remain available. Its corrected recipe
has2297 nonwhite characters,8.8% below the corrected771-digit recipe.
State renaming reduces payload bits; changing numeral notation reduces
printed symbols. See
[SEED_COMPRESSION54.md](SEED_COMPRESSION54.md) and
[SEED_PREDICTORS54.md](SEED_PREDICTORS54.md) for those distinct gains, and
[INITIALIZATION_CORRECTION.md](INITIALIZATION_CORRECTION.md) for the
earlier transition-only calibration gap and its full tile-level repair.

The displayed `equation.pdf` and its TeX source are maintained research
outputs. After a substantial improvement to the displayed construction,
update them to the checked new equation and state its exact domain and
size tradeoffs. Minor circuit changes need not trigger a new rendering.
Preserve the previous page for comparison, and print the complete fixed
constant recipe on the updated page; an external coefficient table or
program is not a substitute for that recipe.

The [twelve-positive polarized equation](candidates/free-j-polarized-positive/README.md)
has96 live operations and exact degree70, improving the earlier100-operation
[ordinary-norm form](research/ordinary-unit-products/README.md). It materializes and checks an
arriving manuscript's ordinary-norm reduction, including its early rank
bound and two-way witness reconstruction. The coherent compact44 tuple is
retained; native calibration and the internal-ZFC proof remain separate.
Its [thirteen-positive companion](research/ordinary-unit-products/ORDINARY13.md)
has90 operations and exact degree51, lowering the preceding90/55 form's
degree at the same arithmetic cost.
The [Hilbert Tenth root-elimination transfer](candidates/fixed-root-elimination/README.md)
also gives fourteen-positive73-operation/degree342 and75-operation/degree293
equations, with a separately reviewed signed-root reconstruction.
Its [centered extension](candidates/fixed-root-centers/README.md) now gives
74/312 and76/191, including an ordinary strong-root integrality proof that
uses the early Pell bound before extracting either deleted root.
Over unrestricted integers, a
[centered joint-guard equation](candidates/joint22-centered/README.md)
has22 unknowns, degree14 and119 operations. Its complete integer zero set
is carried bijectively to the parent by an explicit polynomial shear.

The latest [size comparison](PROPOSAL_REVIEW_LATEST.md) records
[shared odd-rank](research/nine-folded-shared-odd-rank/README.md) nine-positive
405/1,191,570 and compact54 413/1,316,546 forms, plus a lower-degree
[position-zero](candidates/position-zero-norm-sharing/README.md)1,056/997,810 choice. The earlier953/999,518 remains a different cost option.
The [index-weight ten-positive equations](research/ten-positive-index-weight/README.md)
reach 98/360 with a zero-offset scaled base and shared muY, or 103/332
with a direct positive main-base input. The earlier expanded-transport
98/368 and 103/340 graphs remain preserved.
Its strong and auxiliary Pell equations recover the
omitted main root; a strict bound on the entire projection product excludes
extra branches. The former122/816 evaluator remains frozen;
eleven-positive111/211 is a different tradeoff.
Exact [shared norms](candidates/interpolation-shared-norms/README.md) give
thirteen-integer184/1,072.
[Fixed-prime separation](PROPOSAL_REVIEW_VALUATION_INTEGER12.md) and
[identical shared norms](candidates/valuation-shared-norms/README.md) lower
the twelve-integer choices to208/2,400 and202/2,912.
[CRT/valuation composition](reviews/congruence-certificates-peer.md) adds
fourteen-integer148/414 and sixteen-integer118/124 tradeoffs. It also
reduces the13-positive form to88/51 by freeing J. The preserved13-positive
page retains its90/51 evaluator.

The latest [ten-square-frame quartic family](research/power3-square-frame-source-prototype/README.md)
reaches 554 integer unknowns with 6,927 terms at degree four. It also offers
574-variable/height-964,213 and 573-variable/height-45,769,613 choices. Its
ordinary proof recovers a signed power output after orienting its actual
Pell pair, then restores every delayed prefix condition. Full equations,
inverse certificates and quartic coefficients pass independent checks and
rebuilds; see the [combined root review](reviews/power3-square-frame-root-peer.md).
This saves three variables and fourteen terms over 572/7,211 at the same height.

The [factorial-bound quartic family](research/factorial-radius-guard-profile/README.md)
now reaches607 integer variables, or612 with coefficient height964,213
and611 with height45,769,499. These complete degree4 equations have
independently checked integer inverses and every coefficient; the ordinary
76-predicate proof is applied only after source restoration.

The latest [paired-guard quartic family](research/paired-index-guard-profile/README.md)
reaches610 integer unknowns with10,053 terms, or611/613 with8,717/8,622
terms at the same coefficient height2,445,790,974,704. Its639-variable
lower-height companion has5,605 terms at height63,905,891. Exact integer
restoration and the ordinary77-guard proof precede the inherited source
calibration. The earlier78-guard families remain preserved below.

The direct C222 route now supplies complete
[integer quartics in613/614/616 variables](candidates/projected-radius-comparison-base/README.md),
with10,013/8,677/8,582 terms and common height2,445,790,974,704. Its
642-integer companion has5,565 terms and lower height63,905,891. Complete
integer restoration precedes the signed comparison-base theorem. A
nonpointwise lift fixes all78 retained guard values and supplies fresh
witnesses for the new positive comparison parameter before reaching the
frozen904/967 equations. The
[natural factorial-radius family](candidates/projected-factorial-radius/README.md)
now reaches399 variables,8,286 terms and height83,843,274, with complete
support/height alternatives. All are exact quartics with ordinary literal
coefficients, independent of K215 and Jones.

Retaining arithmetic wires now gives
[integer quartics with coefficient height427](candidates/retained-radius-comparison-base/README.md):
1,493 variables and4,981 terms. Further exact projections give846
variables/3,813 terms/height4,750, and701/637/623-variable choices with
larger coefficients. The623-variable profile has8,889 terms and height
938,261. The complete integer bijection and all signed inverse certificates
are independently checked. These are coefficient/variable/support tradeoffs;
the complete ten-positive page remains the displayed equation.

The [407/888/917 review](PROPOSAL_REVIEW_QUARTICS407888.md),
[1,190-integer projection](candidates/synchronized-signed-projections/README.md)
and earlier synchronized/batched families remain reproducible checkpoints.
Full ordinary proofs, normal/optimized finite replays and independent root
reviews distinguish the new arithmetic transformations from their named
C222/refutation calibration. Internal formalization remains open and Lean
remains paused.

The [two parity-family reviews](PROPOSAL_REVIEW_PARITY_FAMILIES.md) add
fifteen-integer128-operation/degree204 and124/352 choices, and
sixteen-integer119/112 and115/160. Both retain the complete calibrated
source34 tuple; their root/sign recovery and finite replay scopes are
recorded separately.

## Approach and comparison

There is no single established meaning of "simplest": number of variables,
total degree, arithmetic operations, and coefficient size give different
answers. We compare these measures separately, retaining constructions
with different tradeoffs, including direct quartics and proof-certificate
encodings. Global optimality is not asserted.

The new [wave11 review](PROPOSAL_REVIEW_WAVE11.md) covers arrivals
`c1a102936a` and`9a33342a03`, including stronger eleven-positive forms,
the saturated ten-integer equation and smaller signed-domain quartics.
It distinguishes full release replays from selected component audits.
The [Hilbert Tenth transfer note](SIZE_RESEARCH_H10.md) explains the
root-elimination arguments and their completed fixed-blank specialization.

Neither a K215 encoding nor a Jones universal equation is a requirement.
Direct proof-certificate and arithmetic-trace encodings are separate research
routes. The nine-variable comparison below is one working branch of a
multi-measure search, not a restriction on the final construction.

A direct parent-index checker for the actual sealed ZFC calculus now has
Lean soundness and completeness, with explicit axiom/schema tags and no
K215 or Jones dependency; see
[ANNOTATED_PROOF_CHECKER.md](ANNOTATED_PROOF_CHECKER.md). Its
[natural-number coding](ANNOTATED_PROOF_CODE.md) now passes Lean, including
roundtrips and malformed-input rejection. Exact numeric certificates for
renaming under binders, including shift and instantiation, also pass Lean;
see [ANNOTATED_RENAME.md](ANNOTATED_RENAME.md). The complete numeric renaming
validator now has a supplied, checked primitive-recursive program for all
input codes; see [ANNOTATED_RENAME_VALIDATOR.md](ANNOTATED_RENAME_VALIDATOR.md).
The exact additive formula bound and universal sealing now also have supplied
programs and numeric certificates; see [ANNOTATED_BOUND_SEAL.md](ANNOTATED_BOUND_SEAL.md).
The actual Separation and Replacement schemas now have checked constructor,
rename and sealing programs too; see [ANNOTATED_SCHEMAS.md](ANNOTATED_SCHEMAS.md).
[Context validation, shifting and the assumption rule](ANNOTATED_CONTEXT_RULE.md)
now have supplied numeric programs too, including soundness for arbitrary raw codes.
[Shared validated coordinates and literal output/premise programs](ANNOTATED_RULE_COORDINATES.md)
now cover all17 original rules.
The [complete numeric logical scanner](ANNOTATED_LINE_SCANNER.md) now checks
raw numeric proof lines and backward references for every original rule,
with supplied primitive-recursive code and an exact acceptance/provability
equivalence. The [complete sealed-ZFC refutation checker](ANNOTATED_REFUTATION_PR.md)
now includes actual axiom/schema dispatch, the full axiom-context scan and
an exact existential acceptance/refutability equivalence. Its literal
program has83281 nodes, or76313 after certified optimization. These are
program-tree sizes; its smaller shared quadratic graph and internal-model
interpretation remain in progress.
The [literal quartic compiler](OBJECT_QUARTIC_COMPILER.md) now has an actual
ZFC derivation of its source/target no-zero equivalence over the entire
internal omega. The [actual sharp pairing quartic](OBJECT_SHARP_PAIRING.md)
now also has internal totality, functionality and surjectivity proofs,
including unconditional derivations in ZFC. Internal verification of the
full checker encoding remains open. The [actual predecessor, tree projections
and zero-test quartics](OBJECT_NUMERIC_WIRE.md) now also have exact semantics
over every internal natural input, preserving the existing shared-register
expressions and witness counts.
A [complete one-page equation](candidates/one-page/README.md) now specifies
the15-positive-variable P69 and every fixed coefficient using one1294-digit
integer and fixed arithmetic formulas. The printed seed and all four coefficient
values are independently checked. The [arithmetic mode ranks and symbolic
coefficient sum](ONE_PAGE_TUPLE54.md) now bind in Lean to the exact native
table and whole stencil, without expanding the large ports. The full native/internal-ZFC calibration
remains open. Both TeX sources and the one-page PDF are included.
The independent [direct executable quartic](ALTERNATIVE_ENCODINGS.md)
already has a closed external consistency equivalence at degree at most
four; it retains the enumerator's arithmetic graph. Lean now bounds its
natural-variable count by `nu < 2^300000`; the exact count remains unmeasured.
See [NATIVE_QUARTIC_SIZE.md](NATIVE_QUARTIC_SIZE.md) for the checked metadata.
The new [natural-register builder](NATURAL_REGISTER_PROGRAM.md) preserves
sharing before quartic compilation, with one gate witness per stored
register. [Shared-register relations](SHARED_REGISTER_RELATIONS.md) now hide
explicit auxiliary inputs and implement the actual max-square pairing used
by the direct checker, as well as the older enumerator's Cantor pairing.
[Direct quadratic attachment](QUADRATIC_REGISTER_SYSTEM.md) now reduces each
local max-square inverse projection to four witnesses and46 operations;
guarded joint quotient/remainder needs one witness and16 operations. All
have degree at most four. [Composable tree/list graphs](QUADRATIC_TREE_CODE_GRAPHS.md)
now cover the actual numeric checker's predecessor-based projections and
guarded list tail at five witnesses and62 operations each. Recompiling the
complete checker remains open. [Guarded local graphs](QUADRATIC_GUARDED_GRAPHS.md)
also cover the actual list head (seven witnesses,76 operations,degree≤4),
zero tests and conditionals, including nil and found-zero behavior.

Wave-ten packages68–75 have now been reviewed; all eight full normal release
replays pass. They add38-integer quartics, an11-positive degree325/113-operation
equation, and a478-operation nine-positive equation of degree1,379,730.
An exact shared-product rewrite now reduces the compact54-sharp candidate
from443 to440 operations, retaining degree1,845,940 and every coefficient;
see [the new candidate](candidates/gap2082-shared-products/README.md).
This historical operation target is retained as a checkpoint; the current
size-only nine-positive target has433 operations, as recorded above.
The same algebra improves package71 to475 operations at degree1,379,730;
see [the lower-degree rewrite](candidates/order7-shared-products/README.md).
See [the combined wave-ten review](PROPOSAL_REVIEW_WAVE10.md)
for the domain-preserving comparison, coefficient costs and proof boundaries.

Wave-nine placement `a2cd79b912` has now been reviewed. All eight full normal
release replays pass. Within the nine-positive branch, the next delivered
cost target is package 66's 444-operation, degree-1,845,940 form. Package
66's separate [compact54-sharp instance](candidates/gap2082-compact54/README.md)
passes its sealed finite checks at **443 positive / 450 natural operations**
with the same degree. Its counted circuit and source-polynomial binding now
pass Lean. Package
65 offers direct source reuse and lower degree; package 67 reaches degree
1,494,006 at higher cost. See [PROPOSAL_REVIEW_WAVE9.md](PROPOSAL_REVIEW_WAVE9.md)
for the comparison, replay evidence and parallel alternative-encoding work.

The H2082 source arithmetic and its actual nine-variable polynomial now pass
Lean, including sharp port bounds, positivity, word/carry calibration and
unbounded witness construction. See
[GAP_NINE_POLYNOMIAL66.md](GAP_NINE_POLYNOMIAL66.md). Lean also identifies the
literal 443/450-operation DAGs with those polynomials, including all eleven
fixed-leaf recipes and the positive/natural root translation; see
[GAP_CIRCUIT_RECIPE66.md](GAP_CIRCUIT_RECIPE66.md). The cancellation-aware
degree bound of 1,845,940 is checked for both actual polynomials in
[GAP_DEGREE66.md](GAP_DEGREE66.md). Native source calibration and the internal
ZFC theorem remain open.

The previous wave-eight target, now a checked source checkpoint, was
package 59's free-coordinate degree-separated adjunct: nine
positive variables, 473 binary operations, degree 1,910,404 (480 operations
over naturals). It improves both measures over the former package-52 target.
Concrete instances bind that architecture to the entire compact
tuples from packages 54 and 57. The preferred instance of this recipe uses 54's
215,492-byte native tuple, retaining the same operation count and degree.
Its sharpened binding halves the radix floor and divides the threshold
scale by 256, saving one raw stored byte. A checked joint-power
rewrite reduces the same polynomial to 456 positive / 463 natural operations;
see [the candidate artifacts](candidates/split116-compact/README.md).
The selection, alternatives,
full finite replays and remaining proof obligations are recorded in
[PROPOSAL_REVIEW_WAVE8.md](PROPOSAL_REVIEW_WAVE8.md). The current closed Lean
equations remain the certified baseline until a replacement is fully checked.

The new split-form foundations now pass Lean: same-degree coefficient
extraction, the shorter rank's exact carry threshold, mask population,
signed-borrow decoding, coefficient bounds, the free-carrier finalizer,
and the assembled binomial-to-source-coefficient contract.
Their contracts and remaining assembly work are recorded in
[SPLIT116_FORMALIZATION.md](SPLIT116_FORMALIZATION.md).
The literal old-z source, all 89 kernel records and the complete unbounded
nine-coordinate arithmetic source equivalence now also pass Lean. The
equation and exact port hypotheses are recorded in
[SPLIT_SOURCE59.md](SPLIT_SOURCE59.md). The actual nine-variable
`MvPolynomial` and its evaluation/source equivalence also pass Lean; see
[SPLIT_NINE_POLYNOMIAL59.md](SPLIT_NINE_POLYNOMIAL59.md). Lean also identifies
the literal 480-operation natural DAG and its 463-operation replacement
with this polynomial, including all twelve fixed-leaf recipes; see
[SPLIT_CIRCUIT_RECIPE59.md](SPLIT_CIRCUIT_RECIPE59.md). The corresponding
473/456-operation positive DAGs and their exact positive/natural root
translation also pass Lean; see
[SPLIT_POSITIVE_RECIPE59.md](SPLIT_POSITIVE_RECIPE59.md). Native calibration
remains open.

The native arithmetic bridge now recovers the exact first Pell index, the
source register `X=2^R`, the binary block base and the common cubic scale;
see [NATIVE_PELL_POWER.md](NATIVE_PELL_POWER.md). The doubled half-binomial,
population and mask arguments now close the full forward bridge from the
literal source to the [native arithmetic window](NATIVE_SOURCE_WINDOW.md),
under explicit coefficient conditions. The [compact54 local decoder](NATIVE_CLAUSE54.md)
now proves exact empty-cell or single-tile acceptance from arbitrary Boolean
selectors, with no one-hot premise. The [whole-stencil carry step](NATIVE_CONVOLUTION54.md)
now derives pointwise mask tests with all temporal rotation phases retained.
The [origin radix digit](NATIVE_ORIGIN54.md) is now forced to one from the
actual source mask and exact low-MC recipe. The [sparse assignment](NATIVE_SPARSE_DIGITS54.md)
is now reconstructed from the source, including the positive cell count,
exact word, origin and Boolean/capacity bounds. The [literal clause bands](NATIVE_CLEAN_BANDS54.md)
now equal the corresponding local coefficient sums plus the explicit
temporal contribution, including cyclic collisions. The [exact high mask](NATIVE_HIGH_PORT54.md)
and [paired temporal support argument](NATIVE_TEMPORAL_SUPPORT54.md) now
derive the actual local clause-mask zero in every cell before phase alignment.
The coefficient interface remains explicit; phase synchronization, whole
compiler calibration and converse completeness remain open.

The package-52 formalization now checks its literal 60-gate, 22-row source,
all 136 quadratic coefficient records, exact selective positions, sharp
coefficient height, sparse low-mask decoding, ratio reparameterization, and
margin-first finalizer. The complete source-to-binomial-to-finalizer
arithmetic equivalence and literal multivariate-polynomial binding also
pass Lean, with explicit coefficient bounds and exactly nine natural
coordinates. See [SELECTIVE_SOURCE52.md](SELECTIVE_SOURCE52.md). Authentic
native calibration and the internal ZFC derivation remain open; this
checkpoint does not yet replace the closed consistency equation.

The wave-5 and wave-6 report packages explicitly distinguish their new final
equations from an end-to-end Lean certificate. The inherited P67 is a particularly short
candidate: 15 strictly positive witnesses, degree 155, and 67 binary
arithmetic operations. Its fixed coefficient tuple and native-window/Pell
compiler still need a formal semantic bridge. Nine-natural-variable forms
use the already formalized Jones reduction but introduce very large powers.
The ten-unrestricted-integer Sun construction is not formalized here.

The wave-6 packages arrived on `origin/main` during this research and were
merged at `2d7766807b`. Their direct quadratic/Sidon encodings improve the
reported low-variable degree and operation counts substantially; for example,
[package 45](con-zfc-diophantine-forms/45-multioutput/README.md) reports nine
positive unknowns at degree 129,875,980 in 788 operations. These were useful
comparison targets. The executable generic Jones route below
prioritizes a complete checked construction and does not claim to improve
those degree or operation counts.

The first formal route is now checked:

1. A concrete semidecision procedure halts exactly when ZFC has a finite
   refutation. Reuse the checked K215/program endpoint rather than assume
   that its halting predicate is computable.
2. Apply the proved MRDP theorem and Jones quartic compression.
3. Apply the proved nine-variable reduction and fix the ordinary input to
   1, obtaining one polynomial in nine natural variables.
4. Negate the solvability equivalence.

An existential representation chosen with `Classical.choose` is a useful
checked milestone, but is not a materialized explicit coefficient recipe.
These two levels will be reported separately. Likewise, a Lean theorem
about syntactic ZFC consistency is distinct from a derivation *inside* the
repository's object-level ZFC proof calculus. Portability of an arithmetic
argument to ZFC is not itself a checked object-level derivation.
The concrete remaining internalization obligations and the first actual
object-language arithmetic proofs are documented in [OBJECT_ZFC.md](OBJECT_ZFC.md).

See [STATUS.md](STATUS.md) for the current evidence and remaining work.

The main checked result is now
`ExplicitZFC.noNaturalZero_iff_conZFC` in
[ExplicitZFC.lean](Lean/DiophantineConsistency/ExplicitZFC.lean). It uses a
closed, executable nine-variable coefficient recipe and has no consistency,
compiler, program, or representation hypothesis. See
[EXPLICIT_EQUATION.md](EXPLICIT_EQUATION.md) for the equation and proof chain.
The earlier existence-based theorem in [ZFC.lean](Lean/DiophantineConsistency/ZFC.lean)
and its 58-witness quartic alternative remain available as separate milestones.
The checked shift in `PositiveZFC` gives the same variable count over strictly
positive integers. A second closed route in
[DIRECT_GRAPH.md](DIRECT_GRAPH.md) represents source arithmetic directly;
its final degree and operation comparison remains to be measured.

For a concrete small arithmetic circuit, see
[SHORT_EQUATION.md](SHORT_EQUATION.md): a 69-operation, degree-111 polynomial
with 15 positive unknowns, bound to the historical package-36 coefficient
tuple. Lean checks its complete positive zero set against the literal P67
baseline. The native-window compiler connecting those explicit circuits to
ZFC refutations remains to be formalized.

The lower-degree alternative in [SHORT_SYSTEM.md](SHORT_SYSTEM.md) uses
75 operations at degree 68, with the same 15 positive unknowns and fixed
coefficient tuple. Lean proves its degree bound and complete positive-zero
equivalence to P67. Grouping the main norm with the two coupled unit factors
saves two operations over the intermediate 77-operation sum of squares.

The checked tradeoff in [SHORT_FRONTIER.md](SHORT_FRONTIER.md) uses
73 operations at degree 80. It groups the six unit factors into three
residuals and has the same complete positive zero set. The present frontier
includes 69 operations/degree 111, 73/80, and 75/68.
The further reduction in [SHORT_REDUCED_STRONG.md](SHORT_REDUCED_STRONG.md)
uses 76 operations at degree 64. It adds a multiple of another vanishing
residual to cancel leading terms; Lean checks complete integer zero
equivalence to P75. Each of these alternatives uses 15 positive unknowns.

## Executable construction and further reductions

The current computability/MRDP interfaces hide the program and polynomial
inside propositions. Extracting executable polynomial data from those
propositions would require an unjustified elimination from `Prop` into
`Type`. The explicit route builds data-valued arithmetic syntax and
representation constructors, with separate correctness proofs. A
syntax-directed primitive-recursion compiler can then retain its polynomial
data throughout. The proved Jones nine-variable reduction accepts any
normalized quartic, so a direct gate-to-quartic conversion can avoid the
58-witness universal representation during this phase.
The detailed contracts and remaining links are tracked in
[COMPILER.md](COMPILER.md).

The supplied-data route now includes arithmetic graphs, Pell sequences,
power, binomial, factorial, and bounded universal quantification.
[`EquationFromRep.construct`](COMPILER_JONES.md) constructs a normalized
quartic and a nine-variable equation directly from supplied representation
syntax, with a checked equivalence for both presentations.
`ExecutableJones.fromRep` also gives a complete executable syntax path,
including its coefficient readers and index. The concrete refutation program
is now supplied by `DirectEnumerator.program`; `ExplicitZFC` closes the
executable equation construction with the actual syntactic endpoint.

## Reproducing the checked milestones

From the repository root, with Lean and Mathlib 4.32.0:

```sh
lake build DiophantineConsistency.ZFC DiophantineConsistency.ShortFrontier
lake env lean Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/ShortEquationAxioms.lean
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean
python3 Computability/DiophantineConsistency/tools/audit_short_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_sos_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_frontier_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_reduced_strong.py
```

The axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
The finite circuit audit verifies operation count, liveness, source binding,
and exact degree independently of the semantic compiler obligations.

## Source interfaces

* `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`: the literal
  215-state machine halts on blank tape iff `BProv ZFCax_s [] Form.fBot`.
* `Diophantine.Common.MRDPCore`: `MRDP.mrdp`, proved without a DPRM axiom.
* `Diophantine.Paper1982.RecursivelyEnumerableQuartic`:
  `Jones1982.rePred_quartic58`.
* `Diophantine.Paper1982.NineMain`: `Jones1982.nine_unknowns`.

All new mathematical statements must have complete proofs: no `sorry`,
`admit`, or additional axioms. Transitive axiom audits and reproducible
build commands will accompany completed milestones.


The [identical integer14 simplification](candidates/constructive-integer14-shared/README.md)
reduces147 to145 live operations at unchanged degree568. Two complete
`(1+x)-1=x` substitutions preserve the entire polynomial and all six
fixed coefficients. Root reviewed the literal checker, all node maps,
normal/optimized replays and all30 sealed files. The lower-degree
148/414 and lower-cost137/792 alternatives remain useful tradeoffs.
The then-current10-positive105/408 PDF and TeX are unchanged by this minor
integer-domain simplification; Lean remains paused.


The [mixed retained-wire family](candidates/projected-radius-mixed-retained/README.md)
now gives1,580/933/788/724/710 unrestricted integer variables, all at
exact degree4. It keeps all original raw rows and coefficients, proves
A and D nonnegative from four original-row bounds, and copies107 guard
triples into the literal reviewed994 equation, with six fresh Legendre
witnesses for its two remaining guards. The full592-wire map is over
integers. All five collected quartics and complete signed inverses pass
independent and deterministic checks in both Python modes. Heights remain
427/4,750/737,653/737,653/938,261; each matched159-guard sibling loses
156 coordinates,52 rows and780 terms. The smaller706-variable, larger-height
family remains a separate tradeoff. The canonical PDF/TeX and Lean are unchanged.


The [signed main-root reduction](candidates/constructive-integer14-quadratic/README.md)
now reaches14 unrestricted integer variables,121 operations and exact
degree312. Absolute-value Pell folding recovers the missing main norm
before the signed rank bootstrap; a whole-product absolute height bound
resolves the quadratic projection for both signs of H. Explicit integer
n maps preserve zero existence in both directions. The complete proof,
all six original coefficients, universal formula binding, literal35-term
norm, exact leading form and normal/optimized replays pass independent
and root review. This improves both cost and degree over14-integer
137/792,145/568 and148/414, which remain preserved checkpoints. It has
more variables and operations than the then-current10-positive105/408 page,
so that complete PDF/TeX remains the canonical display. Lean is paused.


The [contracted mixed-bound family](candidates/projected-radius-mixed-bounds/README.md)
now reaches988/729/703/701/700 unrestricted integer variables at degree4.
All585 original body rows are unchanged. Restoring592 raw wires over
integers licenses the four actual t,n,A,D row bounds;107 copied guard
triples plus six fresh A/D witnesses give the literal reviewed994 zero.
Every projection restores the entire988 parent first. Independent and
full deterministic normal/optimized checks pass all1177 row identities,
complete coefficients/inverses and15 corruption controls. The700-variable
polynomial has10,437 terms and height2,445,790,974,704;729 retains lower
height63,905,891. Each matched994/735/709/707/706 checkpoint loses six
variables, two rows and28 terms. The710-variable retained-wire option
has much smaller height938,261. Canonical PDF/TeX and Lean are unchanged.


Two [identical prefix rewrites](candidates/constructive-integer14-quadratic-shared/README.md)
reduce the new14-integer degree312 equation from121 to119 operations.
Reusing q² and factoring ell(ell+1)k²=(ell*k)(ell*k+k) preserve the entire
polynomial over every commutative ring. Complete148-to146 node coverage,
all removed private definitions, every named register, the full35-term
norm and all six payloads pass independent root review and both complete
checker/rebuild modes. All33 packet seals pass. The signed ordinary proof
and exact nonzero leading coefficient transfer unchanged. This is a minor
saving within the new signed degree312 route; the canonical10-positive
105/408 PDF/TeX remains the separate lower-variable/operation display.
Lean remains paused.


The [thirteen-integer quadratic trace equation](candidates/integer13-quadratic-trace/README.md)
now uses135 operations at exact degree536, down from184/1072. Normalized
trace gives both CRT congruences before signs, the unscaled guard gives
four-root separation, and signed Pell folding restores the main norm.
The whole-product height proof resolves its quadratic projection, then
explicit unrestricted n maps restore the frozen trace endpoint in both
directions. Root reviewed the entire ordinary proof and independent
literal checker; all four normal/optimized checker/rebuild commands pass,
including the full495-term norm, centered425-term degree calculation,
authentic six ports and all138 original archive members. This improves
both current13-integer cost and degree. At that checkpoint, the10-positive105/408 page remained
a separate lower-variable/operation display. Lean is paused.


The [five exact original-row sign consequences](research/guard-seed-consequences/README.md)
remove two factorial-output guards, the moduli-product and CRT quotient
guards, and one endpoint quotient guard before any arithmetic semantics.
The CRT numerator uses its independently proved defining sums, avoiding
a circular quotient dependency. The [complete102-guard family](candidates/projected-radius-mixed-signs/README.md)
now gives973/714/688/686/685 integer variables, all degree4. A literal
102-triple transfer plus15 new Legendre witnesses restores the full988
parent; all integer projections are reversed first. Root reviewed both
ordinary proofs and independent checkers. Full normal/optimized checks
and rebuilds pass every original-row identity, the975-step sign ledger,
all coefficients and inverses. Each matched988/729/703/701/700 parent loses
15 variables, five rows and73 collected terms at unchanged height. The
smaller-coefficient retained710 family and canonical PDF/TeX are preserved;
Lean remains paused.


The [scalar-carrier twelve-integer equations](candidates/scalar-carrier12/README.md)
now use145 operations/degree1200 and141/1456, improving208/2400 and202/2912
with the same twelve unrestricted variables and all six original constants.
A scalar intersective quintic enforces H|K and excludes zero strong scale;
prime-order separation leaves four roots, and signed folding recovers the
missing main norm before its whole-product projection. The completeness
proof keeps one strong witness fixed while selecting the translated
intersective residue. Direct nonodd step-down is proved from the auxiliary
index polynomial. Full independent ordinary review, separate all-register
ring binding, all495 norm coefficients, exact every-gate leading induction,
whole payloads/parent inventory and final normal/optimized checks pass.
Both degrees are halved; cost falls by63 and61 operations. Canonical
10-positive105/408 PDF/TeX remains the lower-variable/operation tradeoff;
Lean stays paused.


The [nine-positive folded-saturation equations](research/nine-folded-saturation/README.md)
now reach414 operations/degree1,355,142 on the full original31 tuple and
422/1,497,238 on compact54-sharp. Saturating the strong norm with the
first Pell radicand allows a two-root equation; coprimality recovers both
squares, then main-Pell folding recovers C=psi_A(B1). Positivity is proved
before extraction, and finite matrix periods construct positive i,j,n.
Both directions retain the exact source/binomial boundary and whole fixed
tuples. Root read the full ordinary proof/checker and verified every
retained source node, every local algebraic cut, centered identity and
actual-coefficient homogeneous witness in both Python modes; both complete
rebuilds pass and all packet seals are checked. Both cost and degree improve
the matched419/427 parents. Lower-degree higher-cost alternatives remain
separate, and canonical10-positive105/408 PDF/TeX is unchanged. Lean is paused.


Two [exact private sign orbits](research/guard-sign-orbits/README.md)
now replace the U and bootstrap-witness guards. Complete raw/contracted
row identities negate U and its sixteen quotient partners together, or
reflect Zminus1 with its two private wires. The independent A>=2 row
bound excludes Z=0 before reflection; U=0 uses the identity branch.
All100 remaining guard values and all643 semantic-prefix coordinates
stay fixed. The [whole100-guard family](candidates/projected-radius-mixed-orbits/README.md)
has967/708/682/680/679 integer variables at degree4. Normalize private
values first, then six fresh witnesses give the literal973 equation;
reverse all signed projections before that step. Root reviewed the full
proofs/checkers and all normal/optimized checks/rebuilds pass. The679
polynomial has397 rows and10,335 terms at unchanged height2,445,790,974,704.
Each matched973/714/688/686/685 checkpoint loses six variables and two
rows. The retained-wire low-height family and canonical PDF/TeX remain
separate tradeoffs. Lean stays paused.

## Tightened nine-positive folding accepted

The [tightened packet](research/nine-folded-saturation-tight/README.md)
now gives409 operations / degree1,191,572 on the whole original31 tuple
and417 /1,316,548 on the separate compact54-sharp tuple. It improves the
frozen414/422-operation equations in both operation count and degree.
The strong ordinate omits J, the auxiliary quotient uses positive j
without a shift, the carrier is Jn+Q, and the first norm shares its
majorant. A new strict-gap proof forces positive margin before root
extraction; two finite matrix periods and a strict carrier bound construct
all three changed positive witnesses. No tuple or domain is weakened.
The [root review](reviews/nine-folded-tight-root-peer.md) records the full
ordinary proof audit, exact degree argument, all four normal/optimized
checks and rebuilds, and closed artifact seals. This nine-variable result
is a separate tradeoff from the maintained ten-positive one-page equation.
Lean remains paused; no new internal-ZFC endpoint is claimed.

## Direct positive J in the ten-variable equation accepted

The [free-J ten-positive equation](candidates/ten-positive-free-j/README.md)
saves two operations, reaching103 at the same exact degree408 and ten
positive unknowns. The enlarged positive J domain is sound: odd main
index recovery gives p=R before q parity, then odd q would force even J
and even R. Coprimality is used only after this contradiction recovers
even q. The J=1 case constructs fresh positive source61 witnesses and
uses its actual unrestricted-positive-J soundness statement. The whole
original tuple and separately calibrated BFS tuple remain distinguished.
The [root review](reviews/ten-positive-free-j-root-peer.md) and
[independent ordinary review](reviews/ten-positive-free-j-ordinary-peer.md)
record the proof and full literal affine-map/degree checks. All four
normal/optimized checks and deterministic rebuilds passed. This minor
two-operation saving does not trigger a new canonical PDF/TeX rendering;
its complete105-operation page remains available pending a substantial
improvement. Lean remains paused.

## Raw100-guard low-height quartics accepted

The [retained-wire100-guard packet](candidates/retained-radius-mixed-orbits/README.md)
gives complete integer quartics in1559/912/767/703/689 unknowns, at
coefficient heights427/4750/737653/737653/938261. Each saves21 unknowns
and seven quadratic rows over its corresponding frozen107-guard raw
parent, without increasing height. All original raw coefficients remain.
An exact zero-set bijection restores592 triangular monic affine wires
and copies all100 guard triples to the actual frozen967 equation before
using its sign theorem; no fresh witness or sign premise is needed for
the bridge. Each signed projection first restores the whole raw parent.
The [root review](reviews/retained-orbits-root-peer.md) records all1277
row identities, complete coefficient collections, four successful
normal/optimized checks/rebuilds and closed seals. The contracted679
quartic remains a different coefficient-height tradeoff. No new Lean
endpoint is claimed and formalization remains paused.

## Smaller signed fourteen-variable guard accepted

The [guard-reduced equation](candidates/constructive-integer14-guard-reduced/README.md)
has14 unrestricted integer unknowns,117 operations and exact degree312.
It removes the explicit v-square factor from the guard. Its new proof
excludes v=0 by rationalizing the remaining two roots and deriving an
impossible CRT divisibility, before using any weak-scale estimate. Both
integer witness maps regenerate only the four private guard coordinates;
the entire degree256 norm and six fixed coefficients are unchanged.
The full output difference has degree at most304, so the complete
nonzero degree312 leading component survives. The
[root review](reviews/integer14-guard-root-peer.md) records all node/guard/
norm identities, four successful normal/optimized checks and rebuilds,
and closed seals. The [initial research note](reviews/signed14-guard-research.md)
also records why two tempting smaller positivity gadgets fail. Lean and
the canonical ten-positive page remain unchanged.

## Ten-positive102/388 accepted

The [shifted strong equation](candidates/ten-positive-shifted-strong/README.md)
now reaches102 operations and exact degree388 in ten positive unknowns.
It uses I=(i+q²)c² and the shorter transport L=HI+b. The shift preserves
the unconditional lower bound and square-ordinate divisibility; a new
rational-rho bound licenses the smaller transport before parity recovery.
Canonical completeness keeps the strong ordinate and constructs a fresh
positive final n, including zero transport quotient. The complete norm
has a nonzero selected coefficient2^28*beta^224 in degree388. The
[root review](reviews/shifted-strong10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-shifted-strong-ordinary-peer.md)
record the full proof, exact gate/degree/whole-tuple checks, four passing
normal/optimized replays and closed seals. A new complete one-page display
is being prepared for the combined gain over105/408; its predecessor
will be preserved. Lean remains paused.

## Canonical page updated to102/388

The maintained [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) at that checkpoint printed the complete ten-positive102-operation,
exact-degree388 equation, including every fixed constant, on one Letter
page. This batches the direct-J, shifted-strong and shorter-transport
improvements into one update over the preserved105/408 page: three fewer
operations and degree20 lower. The complete436-character seed,62-character
alphabet,943 tiles and closed arithmetic coefficient recipe are unchanged.
The [new page packet](candidates/one-page-shifted10/README.md),
[independent root page review](reviews/shifted10-page-peer.md) and
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the displayed bytes.
Both independent peer modes, renderer replays and full coefficient
reconstruction modes pass; the page was visually reviewed. The previous
[105/408 PDF](candidates/one-page-quadratic10/equation.pdf) and its TeX
remain preserved. Lean formalization remains paused.

## Twenty-one pointwise guard consequences accepted

The [main-root/modulus proof](research/main-root-and-modulus-signs/README.md)
recovers15 main-root signs and six power-modulus signs from the unchanged
raw equations with79 retained guards. Its independent semantic-prefix
proof precedes a strict A>W^W bound, signed-index recovery and negative-root
residue contradiction. Only then does a positive-base power call establish
f0>0 and the final modulus sign. All15 actual exponents are proved positive.
The [root review](reviews/main-root-signs-root-peer.md) and
[independent peer](reviews/main-root-modulus-signs-peer.md) verify the
complete original-row, constructor and21-call ledger; all six root
normal/optimized checks, rebuilds and peer runs pass. At the same body
tuple,79 existing triples and63 fresh Legendre witnesses reach the literal
frozen967 equation. Complete new quartics and signed projections are being
materialized separately; no unverified projected count is added here.
Lean and the current canonical PDF/TeX remain unchanged.

## Fixed root weight lowers ten-positive degree to368

The [weighted-root equation](candidates/ten-positive-weighted-roots/README.md)
has ten positive unknowns,102 operations and exact degree368. It replaces
the full-mu strong shift by I=i*c² and weights only the first root by3.
All signed cancellations are excluded before root extraction: two pairs
would imply mu|8, the third would equate an integer to -1/Delta, and a
zero triple would imply mu|2025, then mu|25 despite mu>=1025. Main folding
then gives the strict bound needed for weighted transport. Canonical
completeness uses the explicit positive shifts i_new=i_old+q² and
n_new=n_old+2*tau. The [root review](reviews/weighted10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-weighted-roots-ordinary-peer.md)
record the full proof and exact circuit/degree/whole-tuple checks. All four
normal/optimized checks and rebuilds pass; the unique leading component
has a positive selected coefficient2^28*beta^184. The prior102/388 packet
is preserved; a complete new page is under review. Lean remains paused.

## Complete79-guard compact quartics accepted

The [materialized compact family](candidates/projected-radius-main-root-signs/README.md)
gives full integer quartics in904/645/619/617/616 variables. The smallest
has376 quadratic rows,10,028 collected terms and coefficient height
2,445,790,974,704; the645-variable point has5,580 terms and height63,905,891.
Every profile saves63 unknowns and21 rows over its matching100-guard
parent at unchanged height. Complete signed inverses first restore all79
guards, then592 raw affine wires. The ordered21-sign theorem supplies
63 fresh witnesses at unchanged body values into the literal967 equation.
The [root review](reviews/main-root-quartics-root-peer.md) records full
coefficient collections, every100 copied/fresh guard-row identity, all
four passing normal/optimized checker/rebuild replays and closed seals.
These are checked whole equations, not estimates from deleting guards.
Lean and the ten-positive display remain separate and unchanged.

## Retained-coefficient79-guard quartics accepted

The [new raw family](candidates/retained-radius-main-root-signs/README.md)
keeps all original coefficients and gives1496/849/704/640/626 integer
variables, with exact degree4 and heights427/4750/737653/737653/938261.
The smallest has386 rows and8,904 collected terms. Each profile saves
63 variables and21 rows at unchanged height against its100-guard parent.
The [root review](reviews/main-root-raw-quartics-root-peer.md) records
the complete1256-row integer bijection into904, all592 affine inverses,
and the composed79-copied/63-fresh-witness transfer into literal967.
All100 target guard rows and every full collected polynomial are checked.
All four root normal/optimized checker/rebuild replays and closed seals
pass. The616-variable compact quartic is a separate height tradeoff;
no new Lean or native calibration endpoint is claimed.

## Comparison-base positivity guard removed existentially

The [comparison-base proof](research/comparison-base-sign/README.md) permits
negative B and then lifts it to a positive comparison base while preserving
all78 other guard values. Its complete1177-row audit accounts for62 private
coordinates,141 unit gates and every46 affected nongate constraints. The
signed-index and21-sign proofs precede the lift; q4 positivity is supplied
at the new tuple, not asserted at the old tuple. Three fresh Legendre
witnesses reach the literal904 source. The [root review](reviews/comparison-base-sign-root-peer.md)
and [independent peer](reviews/comparison-base-sign-peer.md) record full
normal/optimized author and peer replays, all passing. New compact/raw
quartics are being materialized separately; this theorem alone supplies no
new projected coefficient count. Lean remains paused.

## Positive short projector reaches101 operations at degree368

The [short-projector equation](candidates/ten-positive-short-projection/README.md)
uses ten positive unknowns and101 live operations at exact degree368.
Kpos=X(3c-2X)+2 is positive after main folding and obeys
Kpos=H*X*c-2*Kquad. Only2 is cancelled modulo odd H; P is retained in
the whole-product argument. Every old positive zero maps to a new one
by the strictly positive shift n_new=n_old+3*(Kquad/H)-X*c. The
[root review](reviews/short10-root-peer.md) and [independent ordinary peer](reviews/ten-positive-short-projection-ordinary-peer.md)
check the full unbounded proof. All four root normal/optimized checker
and rebuild replays, complete53-entry seals and full coefficient binding
pass. The entire polynomial change has degree at most360, preserving the
degree368 leading component. A complete one-page specification is being
reviewed for the next canonical PDF/TeX update. Lean remains paused.

## Canonical complete page updated to101/368

[equation.pdf](equation.pdf) and committed standalone [equation.tex](equation.tex)
now print ten positive unknowns,101 operations and exact degree368. This
batches the fixed root weight and positive short projector: one operation
and20 degrees below the preceding canonical102/388 page, with the entire
constant recipe unchanged. The [complete new page](candidates/one-page-short10/README.md)
includes all436 seed characters,62-symbol alphabet and943 tiles. The
[independent root page review](reviews/short10-page-peer.md) binds all101
live gates universally, verifies all four full ports, and records passing
normal/optimized page peers, renderer replays, author reconstructions and
27 closed seals. The full rendered page was visually checked. All prior
pages remain preserved; [CURRENT_EQUATION.json](CURRENT_EQUATION.json)
binds the exact canonical PDF, TeX and polynomial. Lean remains paused.

## Complete78-guard compact quartics accepted

The [new compact family](candidates/projected-radius-comparison-base/README.md)
has901/642/616/614/613 integer unknowns, all at exact degree4. The613
profile has375 rows,10,013 terms and coefficient height2,445,790,974,704;
the642 profile has5,565 terms at height63,905,891. Each saves three
unknowns, one row and15 terms at unchanged height against its matching
79-guard predecessor. The [root review](reviews/comparison-base-quartics-root-peer.md)
checks every full coefficient collection and inverse. Complete projection
restoration precedes the signed-B theorem and62-coordinate comparison lift;
all78 guard values stay fixed, while three fresh witnesses guard NEWq4
in literal904. Its21-sign theorem then reaches967. All four root
normal/optimized checker/rebuild replays, nested complete source checks
and34 closed seals pass. The canonical101/368 page and Lean remain unchanged.

## Complete78-guard low-height quartics and independent family peer

The [retained-coefficient family](candidates/retained-radius-comparison-base/README.md)
has1493/846/701/637/623 integer variables at exact degree4, with
heights427/4750/737653/737653/938261. The623 profile has385 rows and
8,889 terms; it saves three variables and one row at unchanged height
against626. The [root review](reviews/comparison-base-raw-quartics-root-peer.md)
records every1255 raw/guard row and901 restriction identity in the exact
1493↔901 integer bijection. Only after complete restoration does the
nonpointwise comparison lift reach904 with fresh NEWq4 witnesses, then967.
All four root normal/optimized checker/rebuild runs and35 closed seals pass.
The [separate family peer](reviews/comparison-base-families-peer.md) independently
checks all ten compact/raw inverse certificates, all raw/guard identities
and62 snapshot recipes. Both focused root replays reproduce its final
receipts and reject nine corruptions. The compact613 family is a separate
height tradeoff. Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Literal constructor prose correction

The [constructor erratum](reviews/main-root-constructors-erratum.md) corrects
two aliases in the frozen21-sign note: raw36=y+1>=1, and
raw86=(t+x+y+M0+2)^(2^23)>=3. Root checked every cited original row.
The431-step constructor certificate already uses those correct literal
rows, so all exponent-positivity, guard and equation conclusions remain
unchanged. Neither constructor has fixed parity from these premises.
Frozen certificates and polynomials are preserved; subsequent proofs use
the corrected descriptions. Lean remains paused.

## Direct positive X and zero-offset research

The [direct-base research](research/ten-positive-direct-base/README.md)
replaces X=wq by X=q+x and adds a delayed divisibility carrier. Its
complete prototype has ten positive unknowns,107 operations and degree340.
The [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
checks the unbounded proof and a separate complete free-ring center cut:
remove the H denominator after whole-product projection, then recover q|X,
then justify X/q⁴ as an integer. Full materialized-candidate verification
is underway; this research checkpoint alone adds no accepted frontier.
The [zero-offset draft](research/ten-positive-zero-offset/PROOF.md) proposes
removing the inner constant offset in the scaled main base. Its stronger
ratio estimate suggests one fewer operation at unchanged degree; independent
review and literal checks are pending. The canonical101/368 page and
paused Lean remain unchanged.

## Complete direct-base107/340 endpoint accepted

The [direct-base candidate](candidates/ten-positive-direct-base/README.md)
has ten positive unknowns,107 live operations and exact degree340. It
replaces X=wq by X=q+x and recovers q divisibility from a new carrier
after the whole-product projection removes H. The [root review](reviews/direct107-root-peer.md)
and [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
verify the complete proof chronology and positive witness map. All four
root normal/optimized checks and rebuilds pass, with61 closed seals,
full four-port binding, universal center/norm identities and an attained
nonzero degree340 coefficient. This lowers degree by28 at six extra
operations relative to101/368. The cheaper complete canonical page stays
unchanged; no global optimum or new Lean endpoint is claimed.

## Bootstrap guard exchange accepted; coefficient benefit still being measured

The [guard-exchange proof](research/bootstrap-guard-exchange/README.md)
replaces base0.T's sign guard by the bootstrap Zminus1 guard, keeping78
guards. Signed-A/B index recovery and four actual source calls exclude
negative A without assuming raw86 even or interpreting a factorial early.
The converse changes one free bootstrap coordinate, six gates and one
constraint. The [root review](reviews/bootstrap-guard-exchange-root-peer.md)
and [independent peer](reviews/bootstrap-guard-exchange-peer.md) check
both whole-source existence maps. Both root author/peer normal/optimized
runs reproduce the final receipts, and all four research seals pass.
Actual coefficient profiling is separate; no new projected count follows
from the exchange alone. The [paired-index proposal](research/paired-index-guards/README.md)
is another unfinished lead, with its exact local factorial/binomial
obligation recorded. Canonical101/368 PDF/TeX and paused Lean are unchanged.

## Complete ten-positive99/368 endpoint accepted

The [zero-offset equation](candidates/ten-positive-zero-offset/README.md)
uses ten positive unknowns,99 live operations and exact degree368. The
stronger directly proved ratio bound permits A=mu*a+1; sharing the
already-needed muY product in A-1=(muY)(X+1) removes a second operation.
The [root review](reviews/zero99-root-peer.md) and [independent ordinary peer](reviews/ten-positive-zero-offset-ordinary-peer.md)
check full fresh canonical completeness, including positive auxiliary T
and final n, and every soundness license. All four root normal/optimized
literal checker/rebuild replays, both focused peer modes and62 closed
seals pass. Complete coefficient payloads, all99 live definitions and the
attained degree368 leading component are bound. This improves101/368 by
two operations. The complete canonical101/368 PDF/TeX is preserved while
minor presentation updates are batched, as requested. Lean stays paused.

## Guard-exchange profile finds no benefit in the tested configurations

The [paired coefficient profile](research/bootstrap-guard-exchange-profile/README.md)
tests both compact/raw sources at five support caps, keeping every setting
and source coefficient except the guarded value fixed within each pair.
All20 profiles in each root normal/optimized replay reproduce the complete
receipts. Integer substitutions verify and every quartic is independently
expanded. The [root review](reviews/bootstrap-profile-root-peer.md) records
unchanged variable/row/support/height metrics and one added term in each
projected exchange. The accepted guard placement is retained. An unrelated
raw baseline order gives a possible613-variable/9661-term point at the
same high coefficient height; a full separate package is under review.
No new accepted frontier follows from this research measurement alone.
Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Default-affine raw613 support improvement accepted

The complete [raw/default-affine613 quartic](candidates/retained-radius-default-affine/README.md)
reduces the expanded support from10,013 to9,661 monomials at the same
613 integer variables,375 quadratic rows, degree4 and coefficient height
2,445,790,974,704. The exact unchanged1493 input uses support8 for both
affine and quadratic restorations. All880 integer restorations and all
9,661 coefficients were independently replayed in normal and optimized
Python, along with both deterministic rebuilds; see the
[root review](reviews/default-affine613-root-peer.md). All78 original
guards remain. This is a new projection configuration, separate from the
bootstrap guard exchange. The canonical one-page equation remains unchanged.

## Combined direct/zero-offset105/340 accepted

The complete [ten-positive105/340 candidate](candidates/ten-positive-direct-zero-offset/README.md)
combines the direct coordinate X=q+x with A=mu*Y*(X+1)+1 and shared muY.
It improves107/340 to105/340; the accepted99/368 candidate retains the
lower operation count. All107 direct-parent and99 zero-offset-parent
definitions are bound to the same literal105 rows. The ordinary proof
retains delayed q-divisibility, and its positive completeness map uses the
same zero-offset kernels. Root replayed all four normal/optimized checks
and rebuilds, all complete payloads and degree340 certificates; see the
[root review](reviews/direct-zero105-root-peer.md). Lean remains paused.
The canonical101/368 PDF is unchanged while these small gains are batched.

## Paired index guard theorem accepted

The ordinary [paired-index proof](research/paired-index-guards/LOCAL_FACTORIAL.md)
replaces raw1214's sign with V>=1 and replaces the two t/k122 index-slack
guards with one guard on their product. The exact local factorial bridge
uses only calls1/5/6 at retained K/shifted-K pairs; call2 is used only
for parity. This gives77 predicates instead of78 before projection. Both
zero-existence directions and full source identities passed author,
independent peer and root review in normal/optimized Python; see the
[root acceptance](reviews/paired-index-guards-root-peer.md). Projected
equation sizes remain a separate task; no count is inferred from this theorem.

## Complete77-predicate quartic profiles accepted

The [paired-guard profile packet](research/paired-index-guard-profile/README.md)
contains20 complete equations, quartics and integer projection certificates.
Its compact support32/16/8 choices have610/611/613 variables and
10,053/8,717/8,622 terms, at common height2,445,790,974,704; the lower-height
639-variable choice has5,605 terms at height63,905,891. Raw projections
reach843/698/636/622 variables at heights4,750/737,653/737,653/938,261.
Every source row, guard predicate, integer inverse and full quartic was
checked before inheriting the77-guard proof. All four normal/optimized
checker/rebuild replays passed; see the
[root review](reviews/paired-guard-profile-root-peer.md). A product wire
produces the same projected quartics. No variable saving is inferred merely
from guard count. The canonical PDF and Lean sources remain unchanged.

## Reflected auxiliary parameter improves the nine-positive family

The complete [reflected-nine packet](research/nine-folded-reflected-parameter/README.md)
uses G=F(A+C+1)-A. It stays positive before margin recovery, is1 modulo C
and -A modulo F. Signed Pell folding gives the same soundness rank; the
actual odd completeness index removes the reflection sign. The original
and compact whole tuples now have408/1,191,570 and416/1,316,546
operations/degree, saving one operation and degree2. Root ordinary review
and all four normal/optimized checker/rebuild replays passed; see the
[root review](reviews/nine-reflected-root-peer.md). All source bindings and
the canonical page are preserved; Lean remains paused.

## One factorial bound replaces two more index guards

The ordinary [factorial-radius guard proof](research/factorial-radius-guard/PROOF.md)
replaces the retained K/shifted-K index slacks by f0>=2, reducing77 to76
source predicates. A seed without its bound is either at its true index
or has the exact collapsed coordinates X=A,Y=1. Literal digit/remainder
and ceiling equations exclude every collapsed branch before factorial
meaning is used. Both old slacks are then restored; conversely f0=K!>=6
supplies the new bound. An independent ordinary/source peer and both
normal/optimized root replays pass; see the
[acceptance record](reviews/factorial-radius-guard-root-record.md). Projected
counts remain separate. The canonical PDF and Lean sources are unchanged.

## Shared minimal reflection saves two more operations

The complete [minimal-reflection sibling](research/nine-folded-minimal-reflection/README.md)
reuses the stored product F-1 and sets G=A(F-1)+F. It preserves positivity
and both residue interfaces while using only two new operations. The nine-
positive whole-tuple circuits now have406/1,191,570 and414/1,316,546
operations/degree. Root reviewed the complete ordinary proof and all literal
checks, then replayed both checker/rebuild modes; see the
[root review](reviews/nine-minimal-reflection-root-peer.md). Full fixed
coefficients and source domains are retained. The canonical PDF is unchanged.

## Complete76-predicate quartics accepted

The [factorial-radius profile packet](research/factorial-radius-guard-profile/README.md)
contains15 complete equations and full quartics, including607 variables
with10,042 terms at height2,445,790,974,704. Fresh raw configurations give
612 variables/8,849 terms/height964,213 and611/8,753/45,769,499. Lower-height
choices reach840/695/633/619 variables at heights4,750/737,653/737,653/938,261.
All have exact degree4. The full source domain, every integer restoration
and every quartic coefficient passed both independent modes and both
deterministic root rebuilds; see the
[root review](reviews/factorial-radius-profile-root-peer.md). Only after
restoring the complete76-predicate parent is its ordinary theorem applied.
No projected count was inferred from guard count. Lean remains paused.

## Exact odd-rank sharing reaches405/413 operations

The complete [shared odd-rank sibling](research/nine-folded-shared-odd-rank/README.md)
reuses the literal source register RankPlusOne in B1=R+RankPlusOne, since
R=RankPlusOne-1. It deletes one private multiplication and preserves the
entire polynomial for every assignment. Both whole-tuple nine-positive
circuits now have405/1,191,570 and413/1,316,546 operations/degree. Full
node/operand inventories, coefficients, norms and attained-degree checks
passed both checker/rebuild modes under root replay; see the
[root review](reviews/nine-shared-odd-rank-root-peer.md). The canonical
page and Lean pause are unchanged.

## Early output-sign recovery reduces the source to75 predicates

The ordinary [output-sign extension](research/factorial-radius-output-sign/PROOF.md)
removes the raw93 guard. The exact unconditional eight-row ideal gives
N=f*r+(f-1)*s+f>=2 from the retained f>=2,r>=0,s>=0 predicates, before
the prefix proof or any power meaning. This restores the sole missing
early sign premise and reaches the actual76-predicate source; the reverse
map forgets that triple. Root reviewed all source coefficients and both
normal/optimized replays; see the
[root review](reviews/factorial-radius-output-sign-root-peer.md). There
are75 predicates before projection. Actual quartic sizes remain a separate
measurement; no new Lean or canonical-page change is made.

## Complete75-predicate quartics accepted

The [output-sign profile packet](research/factorial-radius-output-sign-profile/README.md)
contains17 complete degree4 equations with all integer inverse certificates
and full coefficients. Raw/default-affine support8/16 reaches604 variables
and9,676 terms at height2,445,790,974,704. Lower-height choices include
609 variables/8,823 terms/height964,213 and608/8,739/45,769,499; raw
low-height profiles reach837/692/630/616 variables at heights
4,750/737,653/737,653/938,261. The early missing sign is rederived from
actual source coefficients before prefix closure, then every domain row,
integer restoration and quartic coefficient is checked. Root replayed
both checker and rebuild modes; see the
[root review](reviews/factorial-radius-output-profile-root-peer.md). The
canonical one-page equation and Lean sources remain unchanged.

## Encoded-index sign is recovered:74 source predicates

The corrected [encoded-index proof](research/encoded-index-sign/PROOF.md)
removes raw59's explicit sign guard. Raw59 is not a power argument: its
only source use is E=raw59+1. Early direct signs give M>=1,E>=0 and a
modified642-coordinate prefix supplies the unchanged43-argument frame.
A weak-radix carry argument restores the factorial index bounds; then only
the first ten actual powers, exact binomial digits and the moduli-product
remainder prove M=product(1+fj)>1, hence raw59>=0. This reaches the actual
75-predicate source before using its semantic chain. Full author,
independent peer and root normal/optimized checks pass; see the
[root review](reviews/encoded-index-sign-root-peer.md). There are74
predicates before projection. No projected metric, Lean or page change is
claimed by this source theorem alone.

## Identical-polynomial transport contraction reaches98/103 operations

The complete [expanded-transport graphs](research/ten-positive-expanded-transport/README.md)
have ten positive inputs and98 operations at degree368, or103 operations
at degree340. Expanding W=1+gL moves L*B into the center, saving one
operation with the identical polynomial. The direct version also shares
q(q-1) in its carrier, saving a second. Full literal row maps, recursive
free-ring coefficient identities, whole payloads and all four normal/optimized
checker/rebuild root replays pass; see the
[root review](reviews/ten-expanded-transport-root-peer.md). Every parent
positive witness and ordinary proof step transfers by identity. Lean remains
paused; the canonical101/368 page is unchanged while minor gains are batched.

## Complete74-predicate quartics reach601 integer unknowns

The [encoded-index profile packet](research/encoded-index-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches601
variables,9,661 terms and height2,445,790,974,704. Lower-height alternatives
reach606/8,808/964,213 and605/8,724/45,769,499 (variables/terms/height).
Every original domain row, both directions of the full raw/compact integer
bijection, every fresh signed inverse and every quartic coefficient passed
normal/optimized root replay, along with both deterministic rebuilds. The
modified prefix/frame and independent74-predicate source peer are checked
before semantic calibration; see the [root review](reviews/encoded-index-profile-root-peer.md).
No count was extrapolated from a deleted guard. Earlier families remain
preserved. Lean stays paused and the canonical one-page equation is unchanged.

## Actual power-output sign is recovered:73 source predicates

The [power-output proof](research/pow2-output-sign/PROOF.md) removes the
raw104 sign guard. Exact early rows give B=raw104>=-1 and D=B+2>=1;
the modified641-coordinate prefix and weak frame still bound every
positive base/index. Under B=-1, actual indices t and k122=t+1 are
consecutive. Sign-safe calls0/9 recover the paired seeds, then actual call2
forces a positive residue strictly below its divisor, a contradiction.
No local factorial semantics precede this sign recovery. Both existence
maps reach the actual74-predicate parent before inheriting its theorem.
Root read the full proof and checker and matched author/peer receipts in
both modes; see the [root review](reviews/pow2-output-sign-root-peer.md).
There are73 source predicates. Projected sizes require a separate complete
materialization; the measured601-variable family, canonical PDF and Lean
pause are unchanged.

## Six e13 proposal packages screened with reproducible inert checks

The [six-archive intake](research/incoming-e13c748234/README.md) records
complete hashes,2145 member pins, historical reuse and explicit domain
comparisons. Independent data checks reproduce33 full quartic expansions,
39 supported DAG censuses and54 coefficient bindings in both interpreter
modes. After the source76–110 placement, exact old inputs are read from
pinned Git blobs in memory. Root reviewed the report/checker and matched
both sealed receipts; see the [root review](reviews/incoming-e13-root-peer.md).
Squared/centered factorial and common modular Pell identities are useful
new research leads. The squared-radius transfer has an explicit missing-
K-bound obstruction, so no one-gate compiler improvement is assumed.
Natural395/394 and other advertised endpoint tradeoffs await their own full
ordinary/literal calibration review. The current measured601-integer family
and98/368 ten-positive evaluator are unchanged; Lean remains paused.

## Replaying sealed checks after incoming archive placement

The source76–110 placement removed old incoming ZIP paths. The separate
[compatibility runner](research/historical-archives-compat/README.md) supplies
35 exact hash-checked historical ZIPs temporarily from pinned Git objects,
runs an argv command, then removes only unchanged files it created. Existing
paths are preserved and concurrent wrapper lifetimes are serialized. This
keeps all sealed proof/checker bytes unchanged. For example:

```sh
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/encoded-index-sign-profile/check.py --output /tmp/encoded74-check.json
```

Root read the complete wrapper and replayed both modes of all10 integrity
controls; the frozen601 normal/optimized receipt bytes also match under the
runner. See the [root review](reviews/historical-archives-compat-root-peer.md).
This changes reproduction only, with no equation or Lean change.

## Complete73-predicate quartics reach598 integer unknowns

The [power-output profile packet](research/pow2-output-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches598
variables,9,600 terms and height2,445,790,974,704. Lower-height alternatives
reach603/8,794/964,213 and602/8,710/45,769,499 (variables/terms/height).
Only raw104's guard is deleted. Every original domain row, both directions
of the592-coordinate raw/compact integer bijection, every fresh signed
inverse and every quartic coefficient passed normal/optimized root replay,
as did both deterministic rebuilds. The weak641-prefix/43-frame source
interface and branch-local sign proof precede inherited calibration; see
the [root review](reviews/pow2-output-profile-root-peer.md). All46 corruption
controls fail as expected. Earlier families remain preserved. Lean stays
paused and the canonical one-page equation is unchanged.

## Shifted-t index guard is recovered:72 source predicates

The [shifted-t proof](research/shifted-t-index-guard/PROOF.md) removes raw825's
explicit sign guard. Partial parent proofs first recover104 and the four
other required Pell pairs without using825. The actual choose-one row then
excludes the collapsed shifted-t pair: its numerator is at least b² for
t>=2, while the t=1 ceiling forces a digit at least2. Only after this
contradiction does the signed-index theorem recover825>0. No factorial1
meaning or premature call7 interpretation is assumed. A fresh triple reaches
the actual73-domain parent before using its complete theorem. Root read the
entire proof/checkers and matched author and independent peer receipts in
both modes; see the [root review](reviews/shifted-t-index-guard-root-peer.md).
There are72 predicates before projection. The measured598-variable family
remains current until fresh complete profiles pass. Lean and page unchanged.

## Complete72-predicate quartics reach595 integer unknowns

The [shifted-t profile packet](research/shifted-t-index-guard-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches595
variables,9,586 terms and height2,445,790,974,704. Lower-height alternatives
reach600/8,770/964,213 and599/8,696/45,769,499 (variables/terms/height).
Only raw825's guard is deleted. Every domain row, both directions of all592
raw/compact restorations, every fresh signed inverse and every quartic
coefficient passed normal/optimized root replay and both deterministic
rebuilds. Both the95-identity source checker and independent15-cut peer are
pinned and replayed, with exact call7/t=1 chronology and50 corruption
controls; see the [root review](reviews/shifted-t-index-profile-root-peer.md).
Earlier families remain preserved. This is the direct quartic lane; the
fewer-variable norm/display tradeoffs remain separate. Lean stays paused
and the canonical one-page equation is unchanged.

## Squared-radius RAW prototype: complete finite checks accepted

The [separate RAW prototype](research/squared-radius-source-prototype/README.md)
changes only radius row75 and exchanges f>=2 for f>=K at the same guard
triple. All12 complete equations, signed inverse certificates, quartics and
censuses passed root normal/optimized checks and both deterministic rebuilds.
The default prototype has594 variables and9,588 terms: one fewer variable
and two more terms than595/9,586. No new consistency endpoint is inferred
from that measurement. The complete ordinary source proof and fresh
canonical completeness remain separate review obligations; see the
[root finite review](reviews/squared-radius-prototype-root-peer.md).
The accepted595-variable family, canonical page and Lean pause are unchanged.


## Complete squared-radius equations:594 integer unknowns

The [complete ordinary source proof](research/factorial-square-guard-exchange/FULL_SOURCE.md)
and its independent audit are now accepted and exactly bound to the
[frozen RAW prototype](research/squared-radius-source-prototype/README.md).
All12 materialized quartics therefore inherit the ordinary Con(ZFC)
calibration. The first radius is f² and its one guard is f>=K; the second
radius remains g*t². Direct bounds justify all8 range graphs before product
semantics, and completeness recomputes every radix/frame/Pell witness.
Root replayed both complete source audits in normal and optimized Python;
all receipts match. See the [combined root review](reviews/factorial-square-calibration-root-peer.md).

The default complete degree4 equation has594 integer unknowns,9,588 terms
and height2,445,790,974,704. Lower-height alternatives are598/8,564/964,213
and597/8,504/45,769,495 (variables/terms/height). The595-variable predecessor
has two fewer terms and is preserved. This resolves the preceding prototype's
ordinary-proof obligation without changing its sealed finite-scope flags.
The canonical ten-positive page remains unchanged; Lean remains paused.


## Complete common-radius quartic:591 integer unknowns

The [common factorial-radius proof](research/common-factorial-square-radius/PROOF.md)
keeps72 predicates with both radii f² and the one joint guard f>=K+g.
It derives g>=0 before f, repairs the t=1 shifted-seed argument using g<=f,
and rebuilds every radix/frame/Pell witness for completeness. The exact
RAW binding and a separate invertible integer row operation sharing the
base moduli license all24 checked [RAW/CSE quartics](research/common-squared-radius-source-prototype/README.md).
Root's four ordinary replays, both finite checks and both deterministic
rebuilds all pass and match their seals; see the [combined review](reviews/common-squared-radius-root-peer.md).

CSE support16/default gives591 integer variables,9,657 terms and height
2,445,790,974,704 at degree4. Lower-height CSE choices include596/8,328/964,213
and595/8,232/45,769,613 (variables/terms/height). The594-variable predecessor
has69 fewer terms and is preserved. This is the direct quartic family;
other domains and compact norm equations remain separate tradeoffs.
The canonical ten-positive page is unchanged and Lean remains paused.


## Squared output bounds give 575 integer unknowns

The [64-predicate ordinary proof](research/range-output-square-frame/PROOF.md)
replaces eight range output bounds by their squares, then derives their
quotient signs after positive-power recovery. All earlier seed arguments
keep their required signs; a retained positive ordinate is essential to the
signed-output lemma. Fresh completeness rebuilds the entire new frame and
private Pell data. The exact binding licenses all 24 checked
[RAW/CSE quartics](research/squared-range-frame-source-prototype/README.md).
Root's six ordinary replays, both complete finite checks and both
rebuilds pass; see the [combined review](reviews/squared-range-frame-root-peer.md).

The complete CSE/default equation has 575 integer unknowns, 7,225 terms and
height 2,445,790,974,704 at degree 4: 16 fewer variables and 2,432 fewer terms
than 591/9,657. Lower-height alternatives give 580/5,768/964,213 and
579/5,832/45,769,613 (variables/terms/height). These improve the direct
quartic family; compact norm equations remain separate. All predecessors
are preserved, the canonical ten-positive page is unchanged and Lean is paused.


## An existing square reduces the direct quartic family to 572 integers

The [63-predicate ordinary proof](research/power0-output-square-frame/PROOF.md)
uses the existing square of the first power output in its frame and derives
that output's sign after a separate guarded output orients the t pair.
Both earlier pairing arguments use the replacement support. Fresh
completeness rebuilds the entire new frame and private Pell data.
The [complete RAW/CSE quartics](research/power0-square-frame-source-prototype/README.md)
are exactly bound to that proof; see the
[combined root review](reviews/power0-square-frame-root-peer.md).

The best equation has 572 integer unknowns, 7,211 terms, degree four and
coefficient height 2,445,790,974,704. It saves three variables, one residual
and fourteen terms against 575/7,225 at unchanged height. Lower-height
alternatives give 577/5,754/964,213 and 576/5,818/45,769,613
(variables/terms/height). All 24 full polynomial checks, both independent
checker modes and both root rebuilds pass. The compact canonical page
is unchanged by this quartic step; Lean remains paused.


## Canonical complete page: 98 operations and exact degree 360

The [updated equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) now print the complete ten-positive equation
at degree 360 in 98 operations, improving the preserved 101/368 page by
three operations and eight degrees. The full constant body remains on the
same Letter page in 9-point body type: all 436 seed characters, decoder,
943 tiles and four coefficient recipes are retained verbatim.

The [ordinary index-weight proof](research/ten-positive-index-weight/PROOF.md)
uses the pre-transport inequality k>H to replace HI by kI. Its positive
polynomial n shear proves completeness. A separate direct-base equation
has 103 operations and degree 332. All six root source audits, actual-TeX
parsing, both render modes and full tuple reconstructions pass; see the
[root review](reviews/ten-index-weight-root-peer.md) and
[page evidence](candidates/one-page-index-weight10/README.md).
The selected nonzero homogeneous component proves exact degree rather
than a sampled degree. Every earlier page, including its TeX, is preserved.
Lean remains paused; no global simplicity minimum is claimed.


## Existing-square transport: 97/368 and 102/344 alternatives

The [complete square-weight equations](research/ten-positive-square-weight-tradeoff/README.md)
reuse the existing I² gate in L and delete one multiplication. The ordinary
pre-transport inequality I>k>H preserves soundness; the positive polynomial
n shear proves completeness. Exact source, norm and leading-form checks
give 97 operations at degree 368, or 102 operations at degree 344.
These save one operation against 98/360 and 103/332 while raising degree.
All six fresh root normal/optimized replays pass, with 27 actual-artifact
corruptions rejected in each mode; see the
[root acceptance](reviews/ten-square-weight-root-peer.md).
The canonical 98/360 one-page PDF/TeX is retained, all predecessors are
preserved and Lean remains paused.

## A second signed output reduces the quartic family to 569 integers

The [62-predicate ordinary proof](research/power3-output-square-frame/PROOF.md)
appends the square of output106, uses it only in the frame, and removes
that output's scalar guard. Actual call3 keeps output106. Independent
supports orient its t pair before the signed residue recovers106=f^t>0.
The delayed bound for130 and its five related signs are restored before
later source semantics. Fresh completeness rebuilds the changed frame
and private Pell witnesses. Both common factorial radii remain unchanged.

The [complete equations and certificates](research/power3-square-frame-source-prototype/README.md)
include 24 RAW/CSE configurations. The best has **569 integer unknowns,
363 residuals, 7,197 monomials and exact degree four**, with coefficient
height 2,445,790,974,704. Its 885 signed restorations recover every parent
coordinate; none is unconstrained. Savings vary by configuration, as
recorded in the [combined root review](reviews/power3-square-frame-root-peer.md).
Lower-height CSE alternatives include 574/5740/964213, 573/5804/45769613,
581/5731/938261, 596/5521/737653, 654/4784/737653 and 783/3599/4750
(variables/terms/height). The retained parent is 1454/4791/428.

Both ordinary checker modes, both complete finite checker modes and both
full rebuilds pass fresh root review and match retained author receipts.
All prior packets remain preserved. This improves the direct quartic
family; the canonical ten-positive 98-operation/degree-360 page is unchanged.
Lean formalization remains paused, and equation-size research continues.

## Direct tile indices shorten the complete printed recipe

The [directly indexed standalone page](research/indexed-tile-enumeration/equation.pdf),
with [TeX](research/indexed-tile-enumeration/equation.tex), removes the
sorted-rank computation for the same 943-tile language. The complete
constant recipe falls from 2,393 to 2,343 nonwhite printed characters;
the whole page falls from 3,217 to 3,167. All index explanations, the full
436-character seed and its 62-character alphabet are counted. The page
retains ten positive unknowns, 98 operations, exact degree 360 and the
same one-Letter-page layout.

The new selector order changes K. Its [ordinary proof and root review](research/indexed-tile-enumeration/PEER_REVIEW.md)
rebuild the entire native witness and cofinal rank controller for the new
coherent tuple; they do not transfer old packed words pointwise. All 430
transitions, 943 tile conjugacies, 66,062 native basis identities, four
complete integers and controller unit/order/lift facts pass independent
checks. Eight fresh root normal/optimized build, render, checker and
artifact runs match the author records; each artifact run rejects 40
actual corruptions and passes two complete controls.

This 50-character gain is retained as a research alternative. The canonical
98/360 PDF and TeX stay unchanged until a larger improvement is ready.
Lean remains paused and the reduction goal continues.

## Six shared sums permit six product guards

The [anchored product-guard proof](research/shared-remainder-product-guards/PROOF.md)
replaces twelve scalar sign guards by six quadratic product guards. It
uses only ten exact source row sums and four retained anchor pairs:
r+s=a+b>=0 together with rs>=0 forces both removed signs. The signs are
restored before any existing Pell or source interpretation is invoked.
Every raw arithmetic coordinate, including the complete W/A/Pell data,
stays fixed; only guard witnesses are rebuilt.

The full parent drops from 1,454 coordinates and 1,248 residuals to
**1,436 coordinates and 1,242 residuals**, with 56 predicate graphs.
Fresh root normal/optimized checks and rebuilds pass, as does the
independent peer review; see the [root acceptance](reviews/shared-remainder-product-guards-root-peer.md).
The literal checker verifies 16 source identities and rejects 23 actual
corruptions. A separate audit checks all 118 old/new graphs and the
32 possible abstract anchor selections, with 192 difference identities.
Only the fixed six replacements are materialized.

Projected quartic savings remain to be measured from complete equations
and certificates. The current best checked direct quartic still has
569 integer unknowns. The canonical compact page is unchanged and Lean
remains paused.

## Eight new proposal archives at 45b399ec51

The [static intake](research/intake-45b399ec51/TRIAGE.md) authenticates all
eight archives, 1,693 members and 237 statically indexed Python files.
It records exact read scopes and distinguishes delivered claims from
accepted results. No incoming program was executed for this checkpoint.
An independent root replay verifies every member hash and the AST index.

The most promising new claims are ten-positive 92/283 and 93/278 saturated
Pell equations, a ten-positive 96/266 coprime-fusion equation, and direct
quartics with 517 or 519 integer variables. Complete mathematical and
code reviews are in progress. The current page and accepted comparison
frontier are unchanged by intake alone. New shared-sum, quotient-frame
and transport-majorant mechanisms are recorded as separate research leads.
Lean remains paused; successful substantial compact improvements will
replace the canonical PDF and its standalone TeX after full verification.

## Complete shared-remainder compiler reaches 557 integer variables

The [new complete finite family](research/shared-remainder-product-source-prototype/README.md)
now realizes the separately approved 56-guard source theorem. Its best
checked default has **557 unrestricted integer variables, 363 rows,
6,937 quartic terms and height 2,445,790,974,704**. This saves twelve
variables and 260 terms against the preserved 569-variable equation,
at the same row count and height. All 24 RAW/CSE profiles, complete
coefficient maps, inverse restorations and exact censuses pass fresh
normal/optimized rebuilds and independent checks; 89 corruption controls
are rejected. The default has 879 signed restorations and no unconstrained
deletion. Actual deltas for every configuration are retained in the packet.

The [root acceptance](reviews/shared-remainder-product-source-root-peer.md)
composes these finite results with the exact complete ordinary source
theorem and native calibration. A finite polynomial check alone does not
supply that interpretation. Earlier packets remain preserved. The
compact ten-positive page and paused Lean work are unchanged by this result.

## Significant compact-page improvement: 92 operations, degree 283

The canonical [PDF](equation.pdf) and standalone [TeX](equation.tex) now
print the [complete saturated Pell equation](candidates/one-page-saturated10/README.md):
**ten strictly positive unknowns, 92 operations and exact degree 283**.
This saves six operations and lowers degree by 77 from the preserved
98/360 page. All constants, tiles, the decoder and complete 436-character
numeral fit on the same Letter page in 9-point body type.

The [ordinary proof](research/ten-positive-saturated-pell/PROOF.md)
establishes both directions with fresh positive witnesses, coprime root
recovery and a global attained degree proof. Its whole indexed native
composition licenses the shorter fixed recipe jointly at all four ports.
Independent actual-TeX parsing binds every displayed definition and the
complete boxed equation to all 92 live gates, and verifies every rendered
front glyph and the whole PDF constant body. Normal/optimized source,
renderer, parser and artifact checks pass. See the
[root promotion review](reviews/ten-saturated-pell-root-peer.md).

Separate complete tradeoffs use 93 operations at degree 278 and direct
positive X charts with 98/258 and 99/254. Earlier pages and complete source
packets remain preserved. No global optimum or new Lean endpoint is claimed.

## A derived anchor permits a seventh product-guard exchange

The [new ordinary source proof](research/shared-binomial-digit-product-guard/PROOF.md)
replaces scalar guards on raw123 and raw564 by one product guard. Retained
raw94/raw95 signs and literal rows derive raw91>=1; with retained raw537,
the exact source identity gives raw123+raw564>=1. The product then restores
both removed signs before any inherited source interpretation. Each
direction fixes the whole raw body and rebuilds only guard auxiliaries.

The complete literal parent has **55 guards, 1,433 variables and 1,241 rows**.
Four exact source ideals, every guard graph, full maps and whole inherited
seals pass independent normal/optimized checks with 27 corruption controls.
See the [root acceptance](reviews/shared-binomial-digit-product-root-peer.md).
No projected improvement is predicted: the measured default remains the
557-variable quartic pending a separate full compiler packet. The canonical
92/283 page and paused Lean work are unchanged.

## Reviewed Round14 direct quartics: 517 and 519 integer variables

The [ordinary review](research/intake-45b399ec51/ROUND14_REVIEW.md)
approves the new factorial/carrier architecture and signed-Pell proof
relative to the named inherited C222/refutation contracts. Complete
[scoped reproduction](research/round14-direct-reproduction/README.md)
and fresh root normal/optimized runs rebuild all 34 distinct endpoint
artifacts exactly, including full quartics, signed inverses and integral
translations. The independent static collector rejects twelve actual
data corruptions. See the [root acceptance](reviews/round14-direct-root-peer.md).

The new points are **517 unrestricted integer unknowns, 310 rows, 6,774
quartic terms, height 3,904,267**, and **519 unknowns, 321 rows, 6,253
terms, height 411,060**. Both have exact degree four. All earlier complete
families are preserved. The architecture generators themselves were not
replayed; their frozen raw interfaces and ordinary semantics were reviewed
separately. The unrelated norm branch and Lean were not executed.

The eight newly unpacked manuscript releases now occupy111 through118
under con-zfc-diophantine-forms. Exact historical ZIPs remain readable
from the pinned Git arrival commit; selected adapters authenticate their
whole bytes without restoring them into docs/incoming. This relocation
does not itself approve any other incoming mathematical claims. The
canonical ten-positive92/283 PDF and TeX remain unchanged.

## Reusing the existing b saves one more multiplication

The [complete reused-b extension](research/ten-positive-reused-b-weight/README.md)
gives **91/283, 92/278, 97/258 and 98/254** operation/degree profiles
with ten strictly positive unknowns. It replaces L=k(T+alpha) by the
already evaluated b=c(T+alpha)-R. The ordinary proof bounds b before
transport and constructs a fresh positive n. The changed remainder has
degree six, below all existing center defects, so every exact degree
and nonzero global leading form is preserved.

Independent full proof/code review and six normal/optimized replays pass;
all 152 interfaces and 378 gates, complete parent-row maps and both whole
native tuples are bound. Twenty graph corruptions and 31 malformed
artifacts are rejected. See the [root acceptance](reviews/ten-reused-b-root-peer.md).
This one-operation gain is recorded separately while further changes are
batched; the canonical complete92/283 PDF and TeX remain unchanged.
Lean work remains paused.

## The complete 55-guard source family reaches 554 variables

The [new finite packet](research/shared-binomial-digit-product-source-prototype/README.md)
materializes every RAW/CSE profile of the separately accepted seventh guard
exchange. Its best default has **554 integer variables, 362 rows, 6,927
quartic terms and height 2,445,790,974,704**. Against the preserved557
family it saves three variables, one row and ten terms. Both root checker
JSONs and all four normal/optimized full replay transcripts match the
author exactly; every coefficient, signed inverse and census passes, and
90 actual corruptions are rejected. An independent retained-set audit
checks all24 old/new profiles and their actual three delta classes.

The [root acceptance](reviews/shared-binomial-digit-product-source-root-peer.md)
composes those finite results with the exact complete ordinary source
theorem. All coefficient/term alternatives and earlier equations remain
preserved. The separate Round14 family reaches517/519 variables; this
554 result is progress within the older source pipeline. The canonical
92/283 PDF and TeX and paused Lean work are unchanged.

## Removing the center gives 89/288 and 95/262 tradeoffs

The [complete uncentered packet](research/ten-positive-uncentered-b-weight/README.md)
uses **89 operations at exact degree288**, or95 at degree262 on the
direct chart, with ten strictly positive unknowns. The already folded
odd Pell index excludes the first two auxiliary possibilities; the fifth
index forces a strong enough transport bound to omit Cg altogether.
Positive completeness follows from the exact forward n_new=n_old+Cg
shear; positivity of a reverse shear is not assumed.

The global degree proof is a polynomial cancellation argument with a
uniquely dominant final term and explicit nonzero highest coefficients.
Independent full proof/code review and all six normal/optimized replays
pass, covering every live gate, all four parent routes, both whole native
tuples,10 source corruptions and28 malformed artifacts. See the
[root acceptance](reviews/ten-uncentered-b-root-peer.md).
These save operations with slightly higher degree than their centered
parents. The canonical complete92/283 PDF and standalone TeX remain
stable while further changes are batched. Lean remains paused.

## Pointwise guard compression for both Round14 sources

The [new ordinary theorem](research/round14-pair-guard-compression/PROOF.md)
licenses nine individual pair exchanges in the517 ancestry and eight
in519. Exact common-numerator and factorial/digit identities restore all
removed signs over every unrestricted integer body zero, before source
semantics. Both directions fix the entire body tuple and choose fresh
Legendre witnesses. Mixed and factored source views are proved separately.

Independent normal/optimized checks bind19 exact identities,123 old guard
graphs and complete noncontiguous body maps, and reject28 actual corruptions.
Every old guard auxiliary is checked to occur only in its own guard row;
the appended private Horn body coordinate is retained. See the
[root acceptance](reviews/round14-pair-guard-root-peer.md).
This is an ordinary guard-domain result, with no new materialized equation
or projected count. Existing517/519 quartics and the complete92/283 PDF
and TeX remain unchanged until separate complete candidate checks pass.
Lean remains paused.


## One-word window: mask obstruction and narrower open target

The [complete ordinary review](research/one-word-window-review/REVIEW.md)
proves that alpha=1, and every power-of-two slack, contradicts the retained
native mask population budget before transport is used. The former cyclic
group heuristic does not exclude arbitrary word ties or nonlinear digit
decoding. The [corrected active brief](candidates/ten-positive-scaled-norm/ONE_WORD_WINDOW.md)
now distinguishes those scopes and retains the locally valid selective gap
alpha=(MC AND MF_native)*J-1 as an open compiler target.

Root and independent peer reviewed the full arguments and exact source bytes;
the historical and corrected briefs are preserved in a closed ordinary packet.
See the [root acceptance](reviews/one-word-window-root-peer.md). Transport,
carry/anchor/alignment and a replacement for the independent dummy controller
still require complete proofs. No nine-positive equation, new size bound or
formalization is claimed. The canonical PDF/TeX remain unchanged. Lean stays paused.


## Helper normalization reaches433 integer variables

The [complete centered quartic](research/round15-helper-guard-projections/full-data/joint_helper/centered/equation.json)
has433 integer variables,287 rows,4606 terms and exact degree4, with quartic
height128446 and row height256. It saves3 variables,1 row and18 terms against
the436 parent at unchanged heights. The private-helper inverse may change five
body coordinates before restoring the old signs; the semantic front is fixed.

All author source/full checks and four fresh independent root full checks and
byte-exact rebuilds pass; each collector rejects42 actual corruptions. Root
also checked the entire partial coordinate/row maps,180 matched monic steps,
15 free coordinates and whole calibration bindings. See the
[root acceptance](reviews/round15-helper-guard-projections-root-peer.md).
The plain chart is preserved too, with a14-point quartic-height increase.
Earlier equations and canonical PDF/TeX remain preserved. Lean stays paused.


## Shared Pell cap reaches359 integer variables

The [complete shared-cap quartic](research/signed-pell-cap-projections/data/centered/equation.json)
has359 integer variables,222 rows,6058 terms and exact degree4, with height
128446 and row height256. It removes74 variables and65 rows compared with
the433 helper form, while adding1452 terms. Both forms remain available.

The complete ordinary source theorem now composes with explicit Horn witness
overwrite maps,147 certified monic restorations and the actual free list
[133,135]. Four fresh root collector/rebuild modes and all eight retained
receipt/stdout files exactly match the author; each collector rejects34
actual corruptions. Both whole polynomials, translations, centering and
ordinary/native endpoint bindings pass. See the
[root acceptance](reviews/signed-pell-cap-projections-root-peer.md).
Further cap/guard relaxations remain separate proposals. The compact canonical
PDF/TeX and earlier equations are preserved. Lean stays paused.


## Three further cap simplifications: ordinary proofs accepted

The [unoriented cap theorem](research/signed-pell-cap-unoriented/PROPOSAL.md)
removes the cap lower graph and its pooled error term. A nonzero requested t
excludes the collapsed cap first; signed-center power semantics then recover
the native arithmetic front before fresh positive private witnesses are built.
The [F recovery theorem](research/signed-pell-cap-factorial-output-guard/PROOF.md)
omits F's graph in the current policy by using signed targets and the supported
t pair before its old positivity ledger. The
[current-cap helper involution](research/signed-pell-cap-helper-reflection/PROOF.md)
replaces two helper graphs by one, using four actual private ports.

Root and independent peers reviewed every proof and literal interface; each
ordinary packet is closed. These are separately scoped results. Combining
them requires a fresh source proof, all coordinate/graph maps and independent
checks; no projected count follows by subtraction. The accepted359 quartic,
433 lower-term alternative, canonical PDF/TeX and paused Lean work remain
preserved.


## Ten scalar graphs can share one eight-factor product

The [new current-cap ordinary theorem](research/signed-pell-cap-scalar-product/PROOF.md)
restores ten scalar signs using one strict product of eight nonnegative
factors. Signed-index power analysis first recovers x and the reciprocal
index automatically. Four q-divisible denominator powers are established
before all eleven successor residues, with no premature K/N interpretation.
Only then does the product exclude the remaining eight zero factors.

Root and independent peer reviewed the complete258-line proof and literal
interfaces, including67 source rows,11 whole polynomial ideal combinations
and all30 omitted auxiliary occurrence sets. See the
[root acceptance](reviews/signed-pell-cap-scalar-product-root-peer.md).
Both directions fix the original cap body. F, helper signs and both old cap
policies remain; a future refined-source composition needs a separate proof.
No successor equation or projected saving is claimed. Canonical PDF/TeX and
accepted equations are preserved; Lean stays paused.


## Combined refined cap source accepted

The [complete refined source](research/signed-pell-cap-refined-source/README.md)
now binds the three separately proved cap/F/helper reductions with an explicit
combined chronology. It normalizes the helper first, recovers signed-A target
indices using only absolute bounds and nonzero t, then restores F before
reconstructing fresh positive private witnesses at the unchanged native front.

Four fresh root source collector/rebuild modes exactly match the author;
each collector rejects25 actual corruptions. The full four JSON files, all
graphs/maps/privacy,37 atoms/54 ports,15 norms/18 requests/five moduli and
staged178-identity sign ledger pass. See the
[root acceptance](reviews/signed-pell-cap-refined-source-root-peer.md).
This is a complete ordinary/literal source checkpoint with no new projected
quartic count. The359 and433 alternatives and canonical PDF/TeX remain
preserved. Lean stays paused.


## Partial-sum extension ready for materialization

The [fixed-chart partial-sum theorem](research/signed-pell-cap-pool-grouping/PROPOSAL.md)
and its inert coefficient calculation passed complete root and independent
ordinary/static reviews. Five unrestricted sums uniquely extend each zero
of the accepted centered359 chart, fixing every old coordinate. The exact
row reconstructions and full SOS difference are checked. Two independent
root inert replays match the frozen author records byte-for-byte.

The prospective364-variable/227-row quartic has4574 terms and height128446.
Those are fixed-layout calculations; the complete successor equation is
still pending materialization and independent checks. No optimizer was run
and no survival or global-minimum claim is made. The accepted359 and433
alternatives, canonical PDF/TeX and paused Lean work remain preserved.


## Affine window-gap lemmas reviewed

The [ordinary affine-gap note](research/one-word-window-affine-gap/PROPOSAL.md)
now isolates a bounded transport kernel for gaps whose fixed polynomial
has constant term different from1. It also constructs a different
constant-term-one gap satisfying both local masks, and a separate
large-kernel arithmetic family. Root and independent review accept these
lemmas and their carry-aware limits. Their simultaneous compiler and
controller intersection remains open; no nine-positive equation or
numerical improvement is claimed. Canonical PDF/TeX remain unchanged.


## Scalar-product row-address correction

The new scalar-product note cited two wrong power-row addresses. Its q-base
y+1 and x+1 requests are at old source rows292 and307, respectively;
rows297 and312 belong to different successor-base calls. The intended ports
and ordinary argument are preserved by the [explicit erratum](reviews/signed-pell-cap-scalar-product-row-erratum.md).
Root and [independent review](reviews/signed-pell-cap-scalar-product-row-erratum-peer.md)
checked all18 actual call memberships and both complete lowered requests.
The earlier literal-binding acceptance must be read with this correction.
Frozen packets and delivered equations are preserved; subsequent interfaces
must check the row-to-call membership explicitly.


## Complete grouped quartic:364 variables and4,574 terms

The [delivered grouped equation](research/signed-pell-cap-grouped-quartic/data/equation.json)
and [whole expanded polynomial](research/signed-pell-cap-grouped-quartic/data/expanded_polynomial.json)
now have364 unrestricted integer variables,227 quadratic residuals and
exact degree4, with4,574 terms and height128,446. Five unique unrestricted
sums preserve every old coordinate of the accepted359 chart. The complete
row reconstruction, full SOS difference, whole polynomial under extension,
all seven inherited maps and native calibration pass independent checks.

All five author commands and four fresh root check/rebuild modes pass;
each collector rejects30 actual corruptions and all eight root receipt/stdout
records match exactly. See the [root acceptance](reviews/signed-pell-cap-grouped-quartic-root-peer.md).
The new form removes1,484 terms while adding five variables to the359 form.
It improves the older433/287/4606 alternative by69 variables,60 rows and
32 terms at unchanged heights. The359 form remains the lower-variable
alternative. No optimizer or new source semantics is part of this extension.

This is useful direct-quartic progress, not a significant improvement over
the compact ten-positive page. Canonical equation.pdf and equation.tex stay
preserved under the owner's update policy. Lean remains paused.


## Scalar compression composes with the refined cap source

The [new ordinary composition proof](research/signed-pell-cap-refined-scalar-product/PROOF.md)
now permits the eight-factor replacement at the exact refined source.
Its signed-A, t-only chronology recovers the ten omitted scalar signs,
then restores their graph witnesses on the original unnormalized whole
body. Both directions fix that body, h and every retained witness.

Root and independent review accept the complete proof and literal interface,
including all18 joint call/row/port memberships,168 whole row records and
all367 reflection identities. See the [root acceptance](reviews/signed-pell-cap-refined-scalar-product-root-peer.md).
The earlier row erratum is respected. This is a labelled-policy theorem;
a numeric source and projected equation remain separate work. No numerical
saving is inferred, and canonical PDF/TeX and paused Lean remain preserved.


## Exact cyclic carries and a carry-free compiler obstruction

The [new ordinary one-word note](research/one-word-linear-boolean-window/PROPOSAL.md)
uses the Hilbert Tenth spectral theorem to rule out the specified cofinal
carry-free full-target layout. It also proves exact transport equivalence
to a unique cyclic carry stream in a fixed bounded alphabet, with every
offset collision included. Fixed-period carry schedules retain the same
obstruction; a successful cofinal route needs carry periods unbounded by
a fixed constant.

The [independent root review](reviews/one-word-linear-boolean-window-root-peer.md)
accepts these precise lemmas and local Boolean gate identities. A complete
carry-dependent compiler, fixed coefficients, padding and rank controller
remain open. No nine-positive equation, new numerical frontier or canonical
PDF/TeX update follows. Lean remains paused.


## Affine-square lifts reduce prospective term and coefficient size

The [ordinary affine-square theorem](research/signed-pell-cap-affine-square-lifts/PROPOSAL.md)
uniquely extends the accepted364 chart while fixing every old coordinate.
Root independently checked both complete virtual quartics, every changed
row, full SOS differences and whole-polynomial substitutions. Four lifts
give prospective368/231/4467/98336 (variables/rows/terms/height); six give
370/233/4443/53943, with residual height160 and exact degree4.

See the [root review](reviews/signed-pell-cap-affine-square-lifts-root-peer.md).
These are inert fixed-layout calculations with full coefficient hashes;
a delivered successor remains pending. No optimizer retention or global
minimum is claimed. Accepted equations and canonical PDF/TeX stay preserved,
and Lean stays paused.


## Complete refined-product source accepted

The [literal refined-product source](research/signed-pell-cap-refined-product-source/README.md)
now realizes the complete signed-A scalar-compression theorem. Both maps
fix the original unnormalized399-coordinate body and all retained witnesses.
Seven monic products and one strict graph replace ten scalar graphs.
Its guarded478-coordinate/365-row namespace is a SOURCE count only.

All five author commands and four fresh root source checks/rebuilds pass;
each collector rejects35 actual corruptions, including wrong call-row
memberships. Every whole artifact, map, graph, privacy cut,15norms/18requests/
5moduli/37frame atoms/54ports/11ideals and full calibration pass. See the
[root acceptance](reviews/signed-pell-cap-refined-product-source-root-peer.md).
No optimized quartic count follows yet. Existing359/364 equations, canonical
PDF/TeX and paused Lean work remain preserved.


## Complete refined-product quartic reaches329 integer variables

The [delivered centered equation](research/signed-pell-cap-refined-product-projections/data/centered/equation.json)
and [entire quartic](research/signed-pell-cap-refined-product-projections/data/centered/expanded_polynomial.json)
have329 unrestricted integer variables,216 quadratic rows,5,728 terms and
exact degree4, with height128,446 and residual height256. Against the
complete359 form this saves30 variables, six rows and330 terms at unchanged
heights. The364-variable grouped form retains its lower4,574-term tradeoff.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both collectors reject46 actual corruptions; all
eight full root JSON/stdout records match the author byte for byte. The
actual148 monic steps, two free coordinates, Horn private overwrites,
integer translations, every coefficient and complete source calibration
are checked. See the [root acceptance](reviews/signed-pell-cap-refined-product-projections-root-peer.md).
The fixed policy claims no global optimum. Earlier equations and the
canonical92/283 page remain preserved; Lean remains paused.


## A fused ninth factor removes one source guard graph

The [ordinary fused-product theorem](research/signed-pell-cap-nine-factor-fused/PROOF.md)
replaces r0>=0 and P8>=1 by the single quadratic graph
`(r0+1)P8-1=a9²+b9²+c9(c9+1)`, without another product coordinate.
The retained Qy anchors first recover y>=0; all eight other factors are
proved nonnegative before strict fused positivity restores r0 and all signs.
Both maps fix the whole original unnormalized406-coordinate body and
restore TWO fresh old graph triples. The complete ordinary proof,181literal
rows, all graph/privacy/interface maps and all eleven coefficient identities
pass independent and root review. See the
[root acceptance](reviews/signed-pell-cap-nine-factor-fused-root-peer.md).

The475-coordinate/364-row,24-graph namespace is a declared source policy
only. A complete materialized successor and projected size remain pending;
no dimension saving is inferred from source subtraction. The329-variable
equation, canonical compact page and paused Lean work remain preserved.


## Complete fused-nine source accepted

The [literal fused-nine successor](research/signed-pell-cap-nine-factor-source/README.md)
now materializes the one-graph replacement on the complete original body.
All406 body coordinates/all341 residuals are fixed; the guarded source has
475 coordinates,364 quadratic rows and24 whole graphs. Both old triples
are freshly restored before complete parent calibration. These are source
dimensions only; a projected quartic has not yet been measured.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both checkers reject46 actual corruptions, and all
eight full root JSON/stdout records match the author byte for byte. Root
reauthenticated all228 external/five core pins and twelve exact closed
inventories. See the [root acceptance](reviews/signed-pell-cap-nine-factor-source-root-peer.md).
The existing329-variable quartic and canonical92-operation/degree283 page
remain preserved. Lean remains paused.


## Complete nine-positive equation fits one page

The [complete comparison PDF](candidates/one-page-saturated9/equation.pdf)
and [standalone TeX](candidates/one-page-saturated9/equation.tex) print the
entire nine-positive433-operation, exact-degree1,628,768 equation and
every fixed constant on one Letter page at9-point mathematics/8-point
seed. The full original722-character recipe reconstructs all four native
payloads and eleven signed fixed leaves, including initializer698.

All40 displayed identities/every464graphnode/all85free-port kernel
coefficients,29actualTeX corruptions and three positive controls pass
in normal/optimized checks. Both pure rebuilds reproduce all five derived
files, and all eight fresh root JSON/stdout records are byte-identical.
Actual PDF text, strict overflow checks and separate root/peer visual
reviews pass. Seven closed histories preserve every failed checkpoint.
See the [root acceptance](reviews/one-page-saturated9-root-peer.md).
This is a variable-count alternative with substantially higher cost and
degree; the canonical ten-positive92/283 PDF/TeX remain preserved. No
new Lean or encoded internal-ZFC proof is claimed. Lean remains paused.


## Two support-pair products replace four scalar graphs

The [ordinary exchange](research/signed-pell-cap-support-pair-products/PROPOSAL.md)
replaces four scalar sign graphs for183/184/191/192 by two directly
quadratic product graphs. The abstract signed-cap argument and positive
t-only request first give L=q^t and Qt1=q^(t+1), without their output
signs. Both weighted sums are then strictly positive, so the product
predicates restore every old sign. Four fresh old triples are restored
on the unchanged original406-coordinate body before full parent calibration.

Root and independent full reviews accept the unbounded proof and exact
whole source/privacy/interfaces; see the [root review](reviews/signed-pell-cap-support-pair-products-root-peer.md).
This note emits no new source or quartic and claims no projected size.
The current complete equations, canonical PDF/TeX and Lean pause remain
preserved. The separate fused-nine projection is still being checked.


## A simpler nine-positive printed front is prepared

The [new standalone TeX draft](candidates/one-page-shared-odd9/equation.tex)
uses the already accepted413-operation, exact-degree1,316,546 endpoint.
It retains the same entire722-character native recipe as the completed
433-operation page, saving20operations and312,222degrees. Both complete
ordinary/data and mathematical-page reviews pass, including the fresh
positive i/j/n witness maps, all four entire raw coefficient payloads,
all85 translated free-port kernel terms and the whole444-node graph.
The [sealed assessment](research/nine-page-lower-frontier-assessment/ASSESSMENT.md)
explains why the405-operation original31 endpoint cannot reuse this tuple.

This is mathematical TeX preparation. New actual-TeX/PDF validation,
rendering fit and independent visual checks remain pending; no413PDF
is claimed. See the [root preparation review](reviews/one-page-shared-odd9-mathematical-preparation-root.md).
The completed433comparison, canonical92/283 page and Lean pause remain
preserved while the separate reviewed toolchain is prepared.


## Complete413-operation nine-positive page accepted

The preferred [nine-positive comparison PDF](candidates/one-page-shared-odd9/equation.pdf)
and [standalone TeX](candidates/one-page-shared-odd9/equation.tex) now print
the entire413-operation, exact-degree1,316,546 equation and every constant
on one Letter page at9-point mathematics/8-point seed. It saves20operations
and312,222degrees against the preserved433comparison at the same entire
original722-character recipe. The first render and all five author commands
pass, with no retry, layout change or overflow warning.

Both normal/optimized actual auditors prove all43interfaces/every444node/
all85free-port kernel terms, reconstruct all four whole payloads/eleven
signed fixed leaves, reject34actual TeX corruptions and accept four
harmless controls. Both pure rebuilds reproduce all five rendering files;
all eight fresh root JSON/stdout records match the author byte for byte.
Both actual PDF visual reviews pass. See the [root acceptance](reviews/one-page-shared-odd9-root-peer.md).
The main ten-positive92/283 PDF/TeX, all predecessors and the Lean pause
remain preserved while newer compact proposals undergo separate review.


## Complete fused-nine quartic reaches327 integer variables

The [complete centered equation](research/signed-pell-cap-nine-factor-projections/data/centered/equation.json)
and [entire quartic](research/signed-pell-cap-nine-factor-projections/data/centered/expanded_polynomial.json)
have327unrestricted integer unknowns,216rows,5,718terms, exact degree4
and height128,446 (residual height256). This saves two unknowns and ten
terms against329 at unchanged rows/heights. Actual retained maps account
for every change: six old guard auxiliaries disappear; the existing p8
and three fresh mixed-graph auxiliaries survive. No other old mapped
retained coordinate is lost. The grouped364/4,574-term alternative stays.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both collectors reject54actual corruptions. Every
full root JSON/stdout record is byte-identical to its author counterpart.
All147monic restorations/two actual free coordinates/Horn overwrites,
both integer translations, every coefficient, seven whole baseline charts
and complete native/source calibration are checked. See the [root acceptance](reviews/signed-pell-cap-nine-factor-projections-root-peer.md).
The accepted327equation and all predecessors remain preserved while new
Round16 claims undergo separate review. Canonical92/283 and the Lean pause
remain unchanged.


## Seven new proposal archives: staged compact forms lead the next review

The [closed static intake](research/intake-fd3e384e92/README.md) authenticates
all seven ZIPs from `fd3e384e92`, their 3,294 members and 26 complete supplied
quartic vectors. The [root review](reviews/intake-fd3e384e92-root-peer.md)
independently checks the entire inventories and literal censuses. Data counts
alone do not establish source correctness or equality to a sum of squares.

The leading compact proposals have ten positive unknowns and 84 operations
at degree 436, or 85 operations at degree 328. Both retain all four entire
accepted indexed coefficient payloads. The
[ordinary review](reviews/staged-certificates-compact-ordinary-peer.md)
requires an explicit completeness correction: retain the actual canonical
bound `R>3q` to obtain the positive shifted transport coordinate. The weaker
generic `R>=3` premise does not suffice. The
[static checker review](reviews/staged-certificates-compact-verifier-static-peer.md)
licenses preparation of a separately pinned packet, not execution or endpoint
acceptance. Six omitted placement files are present in the original ZIP;
the incoming tree remains untouched.

The [Round16 review](reviews/round16-shared-caps-ordinary-peer.md) records the
324-variable/208-row/5,808-term proposal and its new source obligations. It
saves three variables against accepted 327 while adding ninety terms. Its
positive representative sum needs a new dependency proof before combining
it with compressed signed guards. The
[SignedFree review](reviews/signed-free-scales-ordinary-peer.md) repairs an
incorrect complete leading form without invalidating its degree-44 witness.

No incoming program was run for this intake. The canonical 92/283 PDF,
complete 413-operation nine-positive page and accepted 327-variable quartic
remain unchanged while the staged 84/85 finite packet and complete page are
prepared. A significant verified improvement will be reflected in the
maintained PDF and TeX, with complete predecessors preserved. Lean remains
paused and the size-reduction goal remains active.


## Doubled product-square equations accepted at84/436 and85/328

The [complete finite packet](research/ten-positive-doubled-product-square/RESULTS.md)
now passes both static reviews, all four released author checks and four
fresh root replays. Every whole root JSON and stdout agrees byte for byte
with the author. The two ten-positive equations use84 operations at exact
degree436 or85 at328, with all four unchanged indexed coefficient payloads.
The repaired ordinary proof explicitly retains canonical `R>3q` for shifted
positive T. The whole source/native interpretation, all actual gates and
full leading forms are bound; see the
[root acceptance](reviews/ten-positive-doubled-product-square-root-peer.md).

Both improve the86/466 comparison in operation count and degree. They save
operations relative to the maintained92/283 page while increasing degree.
The85/328 form is being prepared as a complete-page successor with the same
entire printed constants; no PDF is promoted before its separate formula,
render and visual checks pass. The327-variable quartic is unchanged. Lean
remains paused, and no global optimum or consistency assertion is made.


## Maintained PDF updated to the complete85/328 equation

The [maintained PDF](equation.pdf) and [standalone TeX](equation.tex) now
contain the complete ten-positive doubled product-square equation,85 live
operations and exact degree 328. The simpler carrier/finalizer saves seven
operations against the preserved 92/283 page, with degree 45 higher. All four
fixed integers,943 tiles, decoder, alphabet and 436-character numeral remain
printed in full on one Letter page at the previous font sizes.

Both complete static reviews, all five released author commands, four fresh
byte-exact root replays and independent actual-PDF visual reviews pass.
All 30 printed polynomial cuts cover every 85 gate over four free ports;
the entire constant TeX and PDF suffix are checked. See the
[root acceptance](reviews/one-page-doubled85-root-peer.md) and
[closed replay packet](research/one-page-doubled85-root-verification/ROOT_BINDING.json).
The ordinary proof retains the actual canonical `R>3q` repair and complete
indexed native/controller/refutation interpretation. Every predecessor,
including the complete92/283 page, remains preserved. The327-variable
quartic is unchanged. Lean remains paused and the reduction goal active.
