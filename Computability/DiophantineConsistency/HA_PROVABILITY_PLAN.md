# HA provability of the current consistency equations

The owner strengthened the goal on26 October2026: prove in Lean both the
current Diophantine equivalence and that the equivalence is provable in
intuitionistic Heyting Arithmetic (HA). The owner then clarified that a
Lean proof that an HA proof EXISTS is sufficient. There is no requirement
to print, normalize, serialize or enumerate a literal HA proof certificate.
This supersedes encoded ZFC derivation as the primary remaining target.
Equation-size reduction, frequent detailed commits and normal fast-forward
synchronization with origin/main continue.

## Exact target and established results

For each selected literal polynomial P, the intended endpoint is a Lean
theorem asserting `HA.Proves equivalenceSentence`, with `HA.Proves` meaning
existence of a finite derivation using intuitionistic first-order logic,
the usual arithmetic axioms and the full first-order induction schema.
`HA.Proves` is now defined in [HAProofs](Lean/DiophantineConsistency/HAProofs.lean)
and independently checked. The particular `equivalenceSentence` and its
completed provability theorem remain targets.

The sentence must express, in arithmetic, that P has no positive integer
solution iff the actual sealed-ZFC proof predicate has no refutation.
Use P(x+1) on natural variables, represented as equality of two natural
polynomials, for the positive-domain side. The ZFC side must be an actual
arithmetization of the repository's proof convention, not an uninterpreted
atom named ConZFC. A primitive-recursive function-language extension would
need a proved conservative elimination into conventional HA.

The external Lean equivalence is already closed for the maintained
14-positive/65-operation/degree150 equation and the three accepted
13-positive forms, in
[CurrentPositiveZero2011](Lean/DiophantineConsistency/CurrentPositiveZero2011.lean).
The current scaled auxiliary replacement is also covered by
[CarrierScaledAuxiliary118](Lean/DiophantineConsistency/CarrierScaledAuxiliary118.lean).
Their independent endpoint replays and axiom reports are documented in
the [formalization plan](LEAN_EQUIVALENCE_PLAN.md). A source-authenticated
361-module custom dependency validation has passed at the pinned09eaa
snapshot:191 fresh and170 authenticated reuses. A separate15-command
post-merge refresh also passed; see the
[original replay](reviews/current-positive-zero2011-closure-replay.md) and
[limited refresh](reviews/current-positive-zero2011-refresh-replay.md).
Neither is an HA proof-existence theorem.
The later13-source upstream merge also passed a separately scoped
[94-command refresh](reviews/ha-postmerge-refresh-20261026.md), with191
standard-only reports and353 authenticated reused objects. It includes
the maintained and mixed-carrier endpoints, and preserves the twelve
explicit unchanged-client reuse boundaries.

The [first-norm auxiliary correction](research/thirteen-first-norm-correction92/README.md)
now gives13 positive variables,84 operations and exact degree92. Either
sphere equation first forces P=1, so the correction vanishes; every
positive assignment is retained in both directions. Independent fresh
Lean builds pass eight standard-only reports, and complete normal/optimized
finite audits verify the two leading cancellations and all fixed ports.
See the [root acceptance](reviews/thirteen-first-norm-correction92-root.md).
This trades nine operations for four degrees against13/75/96. Its external
ConZFC equivalence is checked; the HA endpoint remains open.

The [complete normalized product](research/fourteen-normalized-product106/README.md)
now supplies14 positive variables,67 operations and degree106 with the
unchanged current ports. The exact scaled identity and positive delta
preserve every positive zero. Two independent fresh current-source builds
pass six standard-only reports; normal/optimized complete finite audits
verify the full degree, all paid operations and all47313 coefficient bytes.
See the [root acceptance](reviews/fourteen-normalized-product106-root.md).
Its external ConZFC equivalence is checked; its HA endpoint remains open.

The current-port mixed-carrier13-variable variants at72/124 and74/122
also have checked entire-positive-zero maps and closed external ConZFC
equivalences. Their [independent replay](reviews/thirteen-lv-carrier122-root.md)
passed16 standard-only reports, with separate complete finite metric checks.
Their HA proof-existence endpoints remain open alongside the maintained page.
The grouped-square13/77/96 variant likewise has a checked external endpoint
and exact positive identity map to LV72; its
[root replay](reviews/thirteen-grouped-squares96-root.md) retains the separate
finite metric and cached-prerequisite scopes. Its HA endpoint is also open.
The shared-residual13/76/96 presentation is now externally checked too:
it computes exactly the grouped polynomial using one fewer operation.
Its [independent replay](reviews/thirteen-shared-squares96-root.md) passed
eleven standard-only reports and separate complete normal/optimized finite
metric checks. Its HA proof-existence endpoint remains open.
The unit-sphere13/75/96 form now has its own externally checked entire
positive-zero equivalence, preserving all witnesses while changing the
polynomial. Its [independent replay](reviews/thirteen-unit-sphere96-root.md)
passed13 standard-only reports and complete separate finite metrics.
Its HA endpoint remains open alongside the other selected forms.

[ObjectCurrentEquation2011](Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean)
supplies a set-theory-language no-solution sentence with exact arbitrary-model
positive-domain semantics. That work is retained, but the new HA target
needs an arithmetic sentence and intuitionistic derivability. No further
ZF-model-only completion is required merely to satisfy the new goal.

The arithmetic equation sentence is now supplied by
[ArithmeticCurrentEquation2011](Lean/DiophantineConsistency/ArithmeticCurrentEquation2011.lean).
Its `unsolvabilitySentence` compiles the exact current fourteen-variable
successor-shifted expression into the ordinary `0,S,+,*` language. All four
complete coefficient ports are actual compact binary numerals, not free
symbols. Exactly fourteen universal binders close the no-zero formula.
The generic compiler has exact semantics over every commutative semiring;
its natural-number interpretation is precisely no positive integral zero
of the displayed polynomial. Three fresh leaves and ten standard-only
axiom reports passed [independent review/replay](reviews/arithmetic-expression-lean-peer.md).
This binds the equation side. The arithmetic ZFC-checker sentence and the
HA equivalence derivation remain open.

[HADeduction](Lean/DiophantineConsistency/HADeduction.lean) now composes
actual finite HA proofs by concatenating their supporting axiom lists.
[HANegativeStability](Lean/DiophantineConsistency/HANegativeStability.lean)
constructs intuitionistic stability proofs for negations, conjunctions and
universals, with the full context shifted at universal introduction.
Four leaves passed [independent replay](reviews/ha-deduction-stability-lean-peer.md)
and sixteen reports using only `propext` and `Quot.sound`.

[HAEquationStability2011](Lean/DiophantineConsistency/HAEquationStability2011.lean)
binds this to the literal current sentence: HA proves `¬¬NoZero → NoZero`.
Its derivation has an empty context and an empty arithmetic axiom list.
Both leaves passed [independent replay](reviews/ha-equation-stability2011-lean-peer.md)
and four standard-only reports. This proves a particular logical property
inside HA. It does not prove NoZero itself or the consistency equivalence.
In particular, double-negation stability alone does not identify a formula
with its full Gödel–Gentzen translation. The translation comparison for
the complete no-zero/consistency equivalence remains to be proved.

## Two viable proof routes to audit

One route proves, within HA, both positive-witness implications:

```text
an actual coded ZFC refutation -> a positive zero of P;
a positive zero of P -> an actual coded ZFC refutation.
```

Negating these implications yields the requested consistency equivalence
intuitionistically. There is no need to extract a refutation from a double
negation of consistency. A new external witness interface can first expose
the existing arithmetic constructions directly from a supplied refutation,
avoiding the current convenience wrapper's classical double-negation step.
That interface alone will not constitute an HA formalization.

A second route proves existence of a PA derivation and applies a verified
Gödel–Gentzen translation plus HA equivalence to the original sentence.
This may avoid reconstructing every external proof in intuitionistic form.
The desired no-witness statements suggest a negative arithmetic formulation,
but the exact translation/stability obligations must be proved for the
chosen proof-checker formula and equation sentence. A standard-number Lean
iff does not itself provide the required PA derivation. Classical Tarski
validity alone likewise does not establish intuitionistic derivability.

The Foundation library already has the first-order Gödel–Gentzen theorem
in Lean, as well as the Coq port. The small
[FoundationTheoryGG](Lean/DiophantineConsistency/FoundationTheoryGG.lean)
adapter now lifts it to finite theory assumptions, preserving the actual
translated axiom list. Both leaves passed an
[independent fresh replay](reviews/foundation-theory-gg-root.md), with59
prerequisite modules authenticated against their v4.32 build traces.
Arithmetic axiom and induction preservation, syntax interoperability and
the particular target's stability remain separate obligations. See the
[existing API audit](reviews/ha-existing-foundation-api-audit.md).
An existence theorem via general proof translation is acceptable: no
expanded derivation for the enormous fixed integers must be displayed.

## Concrete foundational checks

- `PAHF.PASyntax` has reusable arithmetic syntax and induction axioms, but
  its proof calculus has unrestricted excluded middle. It is PA, not HA.
  The existing type-valued bounded-PA proof trees likewise contain LEM.
  Removing LEM must be explicit in a genuine new derivability relation;
  erasure into PA is only a one-way validation.
- `HAProofs` now supplies that relation: sixteen intuitionistic deduction
  rules with capture-avoiding quantifier side conditions, a finite list of
  conventional arithmetic axioms, and full formula induction. Its
  [author receipt](reviews/ha-proofs-author.md) and
  [independent replay](reviews/ha-proofs-lean-peer.md) record ten axiom
  reports and authenticated reuse of five prerequisite modules. This
  defines genuine HA theoremhood; it is not yet the desired HA theorem.
- The shallow `PA.Model` has induction for every Lean predicate. An
  argument using that stronger semantic bundle must not be mislabeled
  validity in every first-order PA model. Formula-instance induction and
  ordinary external induction are different interfaces.
- `PAHF.PASyntax` is a large monolithic dependency. Any reused object must
  have authenticated source/toolchain provenance. A small independently
  namespaced arithmetic calculus is preferable to pretending a partial
  source extraction is that accepted module.
- Standard Lean axioms in an external audit do not identify which HA
  induction instances or proof rules justify the arithmetic argument.
  Conversely, classical reasoning in the Lean METATHEORY is allowed when
  proving existence of a genuine HA derivation; it must not be silently
  inserted as an HA object-language rule.

## The machine calibration needs its own arithmetic audit

The literal715-digit machine is linked to refutations through
[KEndpoint215](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean) and
[KEndpoint](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean).
The current lower chain is not presented as a direct ZFC proof checker:
`c222_of_zf_refutation` uses C222 semantic completeness, the seed/model
construction and `zf_consistent_of_formSeed`. The final ZF/ZFC transfer
uses `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

These are valid external Lean interfaces at their recorded scope. Their
proofs do not automatically establish arithmetic provability of this
calibration. There is, however, substantial completed internal arithmetic
machinery: `ZFCinPA.ValidatorConsistencyEquivalence` proves the validator
consistency equivalence in IΣ₂ and PA; `LSchema` already supplies internal
ZF/ZFC Choice transport; and `BinaryConsistencyRotation240` proves the
consistency equivalence for the exact represented Rotation240 binary
machine in IΣ₂ and PA. Reuse these results rather than reconstructing them.

The remaining comparison concerns the actual215 table and boot seed,
the changed C222 calculus, and the distinct coded proof conventions.
The user-specified `k225-formal/verification/k215/README.md` explicitly
separates its external endpoint from an internal PA theorem. Its215
candidate counter starts at4; the represented240 validator uses different
startup data and the older254 calculus. No definitional rewrite between
these has been found in the inspected sources. Existing represented
lookup and positive-clock simulation frameworks are useful interfaces,
but their exact215 contracts must be proved. The
[constructive/source audit](research/ha-current-equation-constructive-audit-20261026.md)
records these concrete differences and the searched scope. This is an
open comparison obligation, not a claim of unprovability in HA.

The exact215 graph/step/run specialization is now checked in
[ArithmeticMachineRun215](Lean/DiophantineConsistency/ArithmeticMachineRun215.lean).
The bounded transition graph is compiled from the actual typed decimal table,
not a replacement machine. Its primitive-recursive run is total and unique
at every time of every IΣ1 model, and agrees with the actual whole-tape run
at ordinary natural times. IΣ1/PA prove the closed run-totality sentence;
the closed halting sentence has the exact standard interpretation.
Eight fresh leaves passed [independent root replay](reviews/arithmetic-machine215-root.md)
with24 standard-only reports and124 authenticated cached prerequisites.
The sole decoder change narrows one import; a separate two-leaf regression
retains the external equation endpoint. This is not a full closure refresh.

The [C222 audit](research/ha-c222-internalization-audit.md) gives the missing
all-model witness equivalence explicitly: exact215 halting iff the old C254
history checker accepts falsity. It separates represented C222 checking,
internal logical/seed calibration and actual counter4 runtime simulation.
The changed equality leaf now has a checked
[C254 adapter](../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorGrowG222.lean):
for every internal a,b,c in every IΣ1 model it constructs an actual old-checker
proof code for the literal `growG` formula. Its Sigma0 graph agrees with the
actual C222 definition. Seven fresh main/check/prerequisite commands passed
[independent root replay](reviews/validator-growg222-root.md), with ten
standard-only reports and114 authenticated cached prerequisites. The changed
seed bundle still requires additional internal syntactic interpretation work.
Its literal helper-free syntax now also has checked
[bounded circuits](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticSeedTemplates222.lean)
for req/clos/nks/vrel/bundle222, with exact Nat bindings and arbitrary-internal
IOpen graph correctness. Two leaves passed [independent root replay](reviews/arithmetic-seed-templates222-root.md)
with16 standard-only reports and102 authenticated cached prerequisites.
The repeated matrix/binder c, false code1 and legal a=b,c=0 case are retained.
These are representation results; they do not prove the seed internally valid.
None of these missing statements is supplied by standard-Nat simulation.

The actual calculus now has a checked
[Nat proof checker](../BusyBeaver/Lean/BusyBeaver/ZFC/Code222Proof.lean),
including `C222 n ↔ ∃code, check222 code n=true`. Old raw-tree parsing and
quoting are reused as syntax; new recursive validity and conclusions bind
both changed leaves and MP to the actual C222 definitions. Its
[independent replay](reviews/code222-proof-root.md) passed nine reports.
The [bounded row](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticRow222.lean)
then represents exactly those numeric rule semantics in every IOpen model,
with arbitrary-child standard parser agreement and invalid-tag rejection.
Its [independent replay](reviews/arithmetic-row222-root.md) passed ten reports.
Neither packet assumes old C254 semantic agreement for the changed calculus.

[ArithmeticSequenceHistory](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticSequenceHistory.lean)
separately reuses Foundation's generic primitive recursion. Its fixed
history/value syntax has Sigma1/Delta1 graphs, unique totality, exact
sequence length and all-index lookup equations in every IΣ1 model,
conditional on an explicitly represented total step. Both totality
statements retain that premise. Its
[independent replay](reviews/arithmetic-sequence-history-root.md) passed15
reports. Actual C222 instantiation, whole-code Nat binding, internal seed
calibration and exact counter4 runtime simulation are the next obligations.
These three packets total six fresh leaves over pinned cached prerequisites;
they do not establish the final arithmetic consistency equivalence.

The actual instantiation is now supplied by
[ArithmeticHistory222](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory222.lean).
Its syntax-fixed step graph composes actual div/rem, Cantor projections,
sequence lookups and the C222 row. Child-index bounds make the internal
successor recurrence depend on this evaluator's own preceding values.
It proves represented unique evaluation and an actual closed IΣ1 theorem
of total unique Boolean evaluation, by existing arithmetic completeness.
The [independent replay](reviews/arithmetic-history222-root.md) passed both
new leaves and14 standard-only reports over118 cached prerequisites.
Whole-code Nat agreement with the literal decoder is still separate, as
are the logical seed and exact-runtime consistency calibrations. Total
evaluation alone proves neither acceptance soundness nor HA equivalence.

The [all-code Nat adapter](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory222Nat.lean)
now proves exact agreement with the actual decoder/checker for every code,
including malformed inputs, by strong induction generalized over parser fuel.
It defines no duplicate evaluator and imports old History254 only for generic
div/rem/numeral facts. It binds actual C222 derivability to a witness for the
same fixed represented formula. Both leaves passed
[independent replay](reviews/arithmetic-history222-nat-root.md), with eight
standard-only reports over120 cached prerequisites. Internal seed and exact
runtime calibration remain open; the represented formula now has its actual
whole-code standard interpretation.

[ArithmeticProofConstructors222](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticProofConstructors222.lean)
now supplies all twelve actual rule-node evaluation equations at arbitrary
internal IΣ1 inputs. It uses the new history recurrence, actual growG and
helper-free seed with exactly c≠a,b, including rejected collisions. Its
[independent replay](reviews/arithmetic-proof-constructors222-root.md) passed
both leaves and15 standard-only reports over119 cached prerequisites.
The represented CProv222 logical interface and subsequent seed/calculus
interpretation remain separate work.

[ValidatorProvability222](../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorProvability222.lean)
now provides the fixed Sigma1 represented CProv222 predicate, actual
new-constructor witnesses, and finite Lukasiewicz/Kalmar logic. Its Nat
interpretation is exactly actual C222. The
[independent replay](reviews/validator-provability222-root.md) passed both
leaves and ten standard-only reports over122 cached prerequisites. GrowG
is the actual changed equality rule; rho7 is not assumed. The encoded
calculus's classical logic is separate from HA's intuitionistic proof rules.
The [internal equality core](reviews/validator-equality-core222-root.md)
now derives reflexivity, the helper and specialization, rho7 from growG,
and membership vacuity from the gated seed. Both leaves pass independent
compilation and eight standard-only reports over123 cached prerequisites.
Semantic seed interpretation and runtime remain open.

The [arithmetic translation audit](research/ha-arithmetic-translation-adapter-audit.md)
also fixes the next proof-transfer interface: translate Foundation ordered
arithmetic syntax into the existing conventional PAHF HA, then map actual
intuitionistic proofs. Translated equality/arithmetic axioms and arbitrary
induction require explicit HA derivations. Reuse the existing GG recursion;
do not identify its translated axiom theory with conventional HA by naming.
For the literal universal negative equality, a direct syntax comparison can
remove the translation; arbitrary negative formulas require more than the
already proved double-negation stability.

The syntax portion of that adapter is now checked in
[FoundationPAHFSyntax](Lean/DiophantineConsistency/FoundationPAHFSyntax.lean).
It translates the actual ordered arithmetic symbols into PAHF `0,S,+,*`,
using a capture-avoiding existential definition of strict order. Generic
environment substitution/rewriting and the exact canonical binder,
instantiation, free/open and eigenvariable-shift identities are proved.
Both leaves passed [independent root replay](reviews/foundation-pahf-syntax-root.md)
with15 standard-only reports; all369 source/trace/object pins for the59
Foundation and five PAHF cached prerequisites matched. This is a syntax
checkpoint, separate from arithmetic-axiom transfer.

The logical proof-calculus map is now checked too:
[FoundationPAHFLogic](Lean/DiophantineConsistency/FoundationPAHFLogic.lean)
maps actual intuitionistic Hilbert proof trees to `HA.Derives []`, and actual
finite-context proofs/proof existence to `HA.Derives (Γ.map formula)`.
The concrete intuitionistic endpoint discharges the generic extra-axiom
premise using HA's ex-falso rule; it contains no arithmetic-image assumption.
All shifted quantifier contexts and ordered/duplicate assumptions are
retained. Both leaves passed [independent root replay](reviews/foundation-pahf-logic-root.md)
with14 reports using only `propext` and `Quot.sound`, with67 authenticated
cached prerequisites. Conventional arithmetic axioms, induction and sentence
closure still require their own derivations and comparison.

The first conventional arithmetic derivations are now checked in
[HABasicArithmetic](Lean/DiophantineConsistency/HABasicArithmetic.lean):
equality rules, all six arbitrary-term instances of the actual HA axioms,
safe closure opening/reclosing, and the actual formula-induction rule.
The module uses that induction rule to prove0+t=t and proves t+1=S t
from the addition axioms. Nested/free-parameter checks passed
[independent root replay](reviews/ha-basic-arithmetic-root.md), with19
reports using only `propext` and `Quot.sound`. Seven cached prerequisites
were explicitly reused. Further semiring/order axioms and their translated
induction/parameter closures remain separate work.

The conventional arithmetic library now also includes
[HAAdditiveArithmetic](Lean/DiophantineConsistency/HAAdditiveArithmetic.lean)
and [HAMultiplicativeArithmetic](Lean/DiophantineConsistency/HAMultiplicativeArithmetic.lean).
They derive the semiring identities using HA formula induction and explicit
HA equality chains. Their four-leaf [independent replay](reviews/ha-semiring-arithmetic-root.md)
passed36 reports using only `propext` and `Quot.sound`, with eight/nine cached
prerequisites reused for the two respective pairs. These are actual HA
proofs, not equalities supplied as proof-transfer hypotheses.

[HANaturalCases](Lean/DiophantineConsistency/HANaturalCases.lean) proves
`t=0 ∨ ∃z t=S z` by actual formula induction. Its
[independent replay](reviews/ha-natural-cases-root.md) passed11 reports.
[HAEqualityDecidable](Lean/DiophantineConsistency/HAEqualityDecidable.lean)
then proves `∀x∀y (x=y ∨ ¬x=y)` by one formula induction and the predecessor
split, with arbitrary-term instances and full context shifts through
existential elimination. Its [independent replay](reviews/ha-equality-decidable-root.md)
passed14 reports. Both packets use only `propext` and `Quot.sound` (or no
axioms); equality decidability supplies no general excluded-middle rule.
Translated Foundation arithmetic axioms, induction and the final target
comparison still require explicit derivations.

The first concrete translated-axiom checkpoint is now proved in
[FoundationHAArithmetic](Lean/DiophantineConsistency/FoundationHAArithmetic.lean).
Each of the eight semiring equation axioms has an actual
`HA.Proves (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.<name>ᴺ)` endpoint.
Constructive double-negation introduction precedes universal closure;
the fixed source list's membership and every literal syntax image are
checked. No arithmetic-image predicate or desired-provability hypothesis
is supplied. Its [independent replay](reviews/foundation-ha-arithmetic-root.md)
passed22 reports using only `propext` and `Quot.sound`, with88 cached
prerequisites. All76 Foundation records exactly match the already accepted
arithmetic215 inventory. Equality-theory cases, nine order/geometric axioms,
arbitrary induction and the source's parameter closure remain separate.

[FoundationHAEquality](Lean/DiophantineConsistency/FoundationHAEquality.lean)
now discharges every actual source equality-theory axiom's literal GG image,
including all four functions and both relations. HA's proved equality
decidability supplies equality-specific stability; order congruence transports
the whole double-negated existential formula without order decidability.
The source's implication conversion reuses the actual Foundation theorem and
checked intuitionistic proof map, retaining its metatheoretic choice dependency.
Both leaves passed [independent replay](reviews/foundation-ha-equality-root.md),
with31 reports restricted to the standard three Lean axioms.

[FoundationHAClosure](Lean/DiophantineConsistency/FoundationHAClosure.lean)
proves the exact identity between the actual source `univCl` GG image and
`closeN φ.fvSup (formula φᴺ)`. A proved canonical-environment identity covers
all `fixitr` counts, including counts below a sparse free variable. Its HA
proof constructor closes an actual proof of the open body, using genuine
universal introduction. The [independent peer replay](reviews/foundation-ha-closure-peer.md)
passed both leaves and six standard-only reports. This closes the parameter
closure comparison; the arbitrary induction body, nine order/geometric
axioms and final target equivalence still require proofs.

[FoundationHAInduction](Lean/DiophantineConsistency/FoundationHAInduction.lean)
now proves the actual GG image of every unrestricted Foundation induction
instance. Its open body uses actual HA formula induction, distinct zero
and successor substitutions, full-context shifts and genuine equality
transport for x+1=Sx under arbitrary nested formulas. Exact source closure
then gives the closed schema member. Both leaves passed
[independent replay](reviews/foundation-ha-induction-root.md), with30
standard-only reports; all85 cached Foundation records match the already
accepted arithmetic215 inventory. No image-provability premise remains.

[FoundationHAOrderBase](Lean/DiophantineConsistency/FoundationHAOrderBase.lean)
also proves the literal zeroLtOne and zeroLe GG images, with a constructive
arbitrary-term zero/predecessor proof and the exact negative disjunction
encoding. Its [independent peer replay](reviews/foundation-ha-order-base-lean-peer.md)
passed both leaves and ten reports using only `propext` and `Quot.sound`.
The [Additive and Witnesses packets](reviews/foundation-ha-order-witnesses-root.md)
now discharge addEqOfLt, addLtAdd, oneLeOfZeroLt and ltTrans too. Ordinary
HA derivations construct actual predecessors under fully shifted contexts;
the negative images lift those implications while retaining double-negated
order premises. Four independent fresh leaves passed50 standard-only
reports with byte-identical author objects. The
[final three order cases](reviews/foundation-ha-order-final-root.md)
mulLtMul, ltIrrefl and ltTri now pass six more independent builds and53
standard-only reports, also byte-identical to the author. Thus all nine
source order images are discharged. The exact no-zero/consistency target
comparison remains a separate obligation.

[FoundationHATheoryTransfer](Lean/DiophantineConsistency/FoundationHATheoryTransfer.lean)
now constructs the required finite assumption discharge and actual
intuitionistic-theory proof map. Its classical adapter reuses the existing
GG theorem with explicit HA proofs of the source images. The concrete
eight-semiring-axiom corollary has no image-provability premise. Both leaves
passed author and [independent peer builds](reviews/foundation-ha-theory-transfer-peer.md),
with seven standard-only reports and byte-identical outputs. This supplies
proof composition. [FoundationHAPeano](Lean/DiophantineConsistency/FoundationHAPeano.lean)
now discharges every actual PeanoMinus constructor and every unrestricted
induction axiom, giving HA proofs of literal GG images of all actual PA,
subtheory and IΣk derivations without image-axiom premises. Both leaves pass
[independent replay](reviews/foundation-ha-peano-peer.md), with nine reports
and byte-identical objects over112 cached prerequisites (85 Foundation).
The actual source PA theorem of the equation/Con(ZFC) equivalence, the
consistency-predicate comparison and C222 seed/runtime bridges remain open.

[FoundationHANoZero](Lean/DiophantineConsistency/FoundationHANoZero.lean)
now proves both HA implications between the existing compiled no-zero
sentence and an explicit Foundation negative-equation sentence's GG image,
for every Expr(Fin n). It constructs HA equalities for source add-one versus
successor and retains exactly n binders. Both
[independent root leaves](reviews/foundation-ha-nozero-root.md) pass27
reports using only propext/Quot.sound. The [literal current binding](Lean/DiophantineConsistency/FoundationHACurrentNoZero2011.lean)
now proves both HA implications for exactly the original
ArithmeticCurrentEquation2011.unsolvabilitySentence and a concrete
Foundation source with14 binders. Seven independent fresh leaves pass18
standard-only reports. An exact40-declaration ownership move into five
narrow data/syntax modules avoids the conflicting global Matrix.map
imports while preserving original names, ports, expression bodies and
all remaining proof text. Internal hygienic macro names can change, so
affected native clients require their own refresh. Neither comparison
discharges source PA equivalence or identifies the final consistency
predicate with its translated image.

[FoundationHACurrentTransfer](Lean/DiophantineConsistency/FoundationHACurrentTransfer.lean)
now composes the completed maps: an explicit PA proof of the concrete
source equivalence yields both HA implications for the maintained sentence
and the translated target. Its negative corollary concludes not GG(rho).
Two [independent fresh leaves](reviews/foundation-ha-current-transfer-root.md)
pass10 standard-only reports with byte-identical objects over133 reused
modules (85 Foundation). No source PA proof or independent consistency
predicate comparison is supplied by this conditional adapter.

[CurrentWitnessEquivalence2011](Lean/DiophantineConsistency/CurrentWitnessEquivalence2011.lean)
now proves the external direct equivalence between positive zeros and
the literal `BProv ZFCax_s [] Form.fBot`. Its final negation composition
uses no double-negation elimination; imported calibration and arithmetic
are not thereby internalized. See the
[root replay](reviews/current-witness-equivalence2011-root.md).

Two bounded arithmetic prerequisites are now checked:
[NativeFiniteCarry](Lean/DiophantineConsistency/NativeFiniteCarry.lean)
constructs the actual quotient carries by at most `57*card(ι)` iterations
in the current radix47 setting, retaining wraparound and reset identities;
[BoundedPellDivisibility](Lean/DiophantineConsistency/BoundedPellDivisibility.lean)
finds a positive divisible Pell ordinate at index at most m², including
the actual fresh-seed shape. Both main/check pairs passed independent
[root replay](reviews/finite-carry-bounded-pell-root.md), with21 standard-only
axiom reports. Their bounded algorithms are standard-arithmetic results,
not yet HA derivations. The frozen current witnesses were not replaced.

Remaining arithmetic refactorings include replacing real-valued Pell
estimates by denominator-cleared integer inequalities. Under the
PA/negative-translation route, each
refactoring should be justified by its contribution to PA formalization;
surface elimination of `Classical.choice` is not the goal by itself.

The actual internal C222 [relational/equality packet](reviews/validator-eind222-root.md)
now supplies finite quantifier and existential deductions, membership
vacuity, fixed-binder alpha conversion and the indiscernibility relation
with both membership transports. The proofs retain arbitrary internal
IΣ1 values, legal zero/equal labels and the auxiliary-binder collision.
Four independent leaves pass24 standard-only reports with byte-identical
author objects. The [next seed witness](reviews/validator-seed-witness222-root.md)
normalizes both literal negative universals by explicit finite deductions,
then obtains `CProv222(∃k(p∈k))` with numeric label k=Eind(p+1,p).
The two independent leaves pass11 reports, including actual Nat p=0.
This is membership containment, not the full native container axiom or
CP/GIC. No arbitrary proof interpretation, seed semantic soundness or
counter4 calibration follows merely from this witness.

The [canonical-data refresh](reviews/current-equation-narrow-root.md)
also independently rebuilds130 affected native clients, with92
standard-only reports, over285 unchanged authenticated objects and five
independently fresh narrow owners. Its420 selected modules include the
actual consistency/witness endpoints and selected frontier checks. The
full478-module inventory and58 outside modules are distinguished; no
whole Foundation or umbrella replay is claimed.

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

The [standard-Nat syntax semantics](reviews/foundation-pahf-nat-semantics-root.md)
now identifies the existing GG/syntax map with the original source
sentence's truth in natural numbers, retaining all binder environments.
Two independent builds pass seven standard-only reports. This is a semantic
comparison in Lean, not an HA derivation. The fixed ZFC proof-convention
comparison still needs its provider-cache audit; available old source and
author build reports are kept separate from authenticated objects.

## Next reviewable checkpoints

The [substitution/opening audit](research/c222-substitution-opening-proposal-20261026.md)
narrows the next actual C222 syntax checkpoint to a Π1/IΣ1 induction,
reusing only unchanged term/vector helpers. Exact opening follows from
source substitution and the accepted shift equation. Numeric equality
needs no fresh-stream premise; later interpreted quantifier transport
retains the explicit IΣ2 alpha and vacuity obligations. Stream selection
and arbitrary proof translation are separately scoped.

The [HA bounded quantifiers](reviews/ha-bounded-quantifiers-root.md) now
have actual HA empty/successor laws and decision proofs from the uniform
object-language premise ∀x.dec a. Genuine simultaneous formula induction
preserves arbitrary nested matrices and all ambient parameters. Two fresh
independent builds pass seventeen propext/Quot.sound-only reports. The
next clients are structural bounded-formula decision and the literal
Foundation/GG bounded-syntax comparison, with actual checker normalization
still separately required.

The [uniform actual C222 alpha theorem](reviews/validator-environment-alpha222-root.md)
is now independently checked for all internal typed source codes, with
an explicit Π2 invariant under IΣ2. Both directions retain the same context,
and both have actual numeric checker witnesses. Two fresh independent
builds pass fifteen standard-only reports. Stream selection and source
substitution/opening precede the later arbitrary proof interpretation.

The [HA interval laws](reviews/ha-strict-intervals-root.md) now prove
the empty interval, s<S s and both actual HA implications for
s<S t iff (s<t∨s=t). Two independent fresh builds pass twelve
propext/Quot.sound-only reports. The
[next bounded-quantifier plan](research/ha-bounded-quantifier-next-leaf-audit.md)
retains arbitrary matrices, bound shifts and a literal uniform decision
formula. It also keeps the actual Δ1 fixed-point proof checker distinct
from a syntactically bounded matrix; that normalization remains unproved.

The [HA strict-order decision](reviews/foundation-ha-order-decidable-root.md)
now proves the actual ordinary decision formula and double-negation
stability for arbitrary terms, with capture-safe transport and finite
contexts. Its independent pair passes twelve reports with only propext
and Quot.sound. Together with the existing equality decision, this supplies
atomic resources for the pending bounded-matrix comparison. A literal
HA proof of the actual checker normalization is still required; classical
Δ1 model equivalences do not provide that proof.

The [finite C222 atomic transport](reviews/validator-atomic-transport222-root.md)
is now independently checked: actual numeric proof witnesses transport
typed equality/membership atoms under the same represented context. Both
fresh leaves pass, with13 standard-only reports. The reverse quantifier
premise explicitly follows weq(t,s)→Eind(t,s)→Eind(s,t); no old-context
exchange is assumed. The next uniform source-formula theorem retains an
explicit Π2 invariant under IΣ2 and all cross-body vacuity resources.

There is now a [closed HA consistency comparison](reviews/foundation-ha-zfc-validator-root.md):
HA proves both implications between fixed GG(Foundation ZFC consistency)
and GG(actual C254 validator consistency). The actual validated PA theorem
supplies the proof, so no source-proof premise remains in this checkpoint.
Two independent fresh builds pass eight standard-only reports. This is an
actual HA proof-existence theorem for those two fixed translated sentences;
the current equation and untranslated-checker comparison remain open.

The [represented Eind-context checkpoint](reviews/validator-eind-context222-root.md)
now provides internal IΣ1 projections, cons equivalences, context vacuity
and binder discharge with actual numeric C222 witnesses. Its independent
pair passes twelve standard-only reports. The primitive equality premise
is composed only in the proved weq-to-Eind direction; all four binder
vacuity resources are retained. Uniform alpha and substitution remain open.

The [fixed ZFC sentence binding](reviews/foundation-zfc-consistency-nat-root.md)
now identifies an explicit GG/PAHF sentence's standard-Nat truth with the
actual syntactic ConZFC proposition, including Choice. Two independent
fresh leaves pass eight standard-only reports over the validated410-module
environment. This semantic comparison is unconditional. HA normalization
to an untranslated checker and the current equation's internal equivalence
remain open.

The actual permuted enumerator now also has independent
[fetch/progress](reviews/arithmetic-command-fetchperm222-peer.md) and
[one-command effect](reviews/arithmetic-command-stepperm222-root.md)
replays. Four fresh commands pass20 standard-only reports. The graphs
range over arbitrary internal IOpen inputs and have all-state/all-raw Nat
adapters. The command permutation, AX order, old-counter dominance, actual
growG/bundle222 and zero-versus-successor result convention are explicit.
Scheduler fairness, internal proof invariants and exact215 simulation
remain open.
The [composed enumerator step](reviews/arithmetic-enum-stepperm222-root.md)
is now independently checked as a total internal IOpen graph, with actual
EnumPerm.enumStep semantics on every ordinary state. Its fresh pair passes
eleven standard-only reports. Full represented recursion, scheduling and
proof invariants remain separate checkpoints.
The subsequent [represented full run](reviews/arithmetic-enum-runperm222-peer.md)
now supplies total/unique recursion at every internal IΣ1 time, the
semigroup law, halt absorption and exact actual EnumPerm.run agreement
for all ordinary states/times. Its independent pair passes thirteen
standard-only reports. The next runtime obligations are a draining bound
for individual candidate words, fair reach from candidate4, proof-state
invariants and exact215 simulation.
The [word-evaluator tick](reviews/arithmetic-command-tickperm222-peer.md)
now proves the required internal remaining-word decrease, retaining
separate halt and successful-completion codes. Its independent pair passes
thirteen standard-only reports and binds every raw Nat command to actual
EnumPerm.cstep. The whole-word draining proof is a separate next checkpoint.
The later [whole-word evaluator](reviews/arithmetic-command-runperm222-peer.md)
now proves the drain bound at all internal IΣ1 word codes, total unique
evaluation, and closed IΣ1/PA totality. Two independent fresh builds pass
twenty-one standard-only reports. Its fixed-word pointwise induction does
not quantify universally over changing work states. Execution composition,
fair reach from candidate4 and the proof invariant remain open.

The [73-module consistency refresh](reviews/fixed-consistency73-root.md)
has now passed, including current R2Native, LSchema and the actual
Foundation consistency equivalence. It retains337 cached prerequisites,
all139 Foundation providers,20 standard-only reports and45 existing linter
warnings. This closes the local provider gap; the fixed standard-Nat
sentence binding and current215/222 arithmetic calibration are separate.

The [uniform typed C222 vacuity theorem](reviews/validator-environment-vacuity222-root.md)
now supplies actual represented proof witnesses for every internal typed
formula under explicit environment/binder avoidance. Its Π2 induction uses
IΣ2 and its independent pair passes11 standard-only reports. This closes
the encoder-vacuity checkpoint while substitution, alpha transport and
general proof interpretation remain open.

The [actual permuted-command parser](reviews/arithmetic-command-wordperm222-peer.md)
now has a represented bounded graph in IOpen and agrees with the literal
Nat decoder on every raw input. Its independent two-leaf replay passes
nine standard-only reports. This respects the0/1/2/AX command layout and
y-then-x packing; shifted fetch, full run simulation and fair reachability
from counter4 remain open.

The owner reaffirmed the **HA target** on26 October after discussing PA.
PA may remain an intermediate theory in the already checked proof
translation; existence of an actual HA derivation is the required endpoint.
The [represented C222 formula encoder](reviews/validator-formula-encoder222-root.md)
now has an independent five-source replay with13 standard-only reports.
Its fixed graph and constructor/SHIFT equations hold for arbitrary internal
IΣ1 inputs. Uniform typed vacuity and arbitrary proof interpretation remain
open. The [fixed consistency cache audit](research/fixed-consistency-nat-cache-gap-audit.md)
has authenticated all139 selected Foundation providers and proposes73
local refreshes; that proposal is not an executed consistency proof.

1. Authentic HA derivability and basic arithmetic/induction interfaces are
   checked, with one-way classical embedding and focused binder checks.
2. The literal equation sentence and a fixed Foundation/GG ZFC consistency
   sentence with its exact standard-Nat proof convention are checked.
   Establish the remaining internal coding comparison to the intended
   untranslated refutation checker.
3. Establish the applicable proof-translation/stability theorem or the two
   direct internal witness transformations. Record which remaining native,
   Pell and machine lemmas need PA/HA proof-existence witnesses.
4. Compose a CLOSED Lean theorem asserting existence of an HA derivation
   of the actual equivalence. A desired-provability hypothesis is not a
   completed endpoint.

No HA proof of the current equation's consistency equivalence is claimed
at this checkpoint.
The decimal equation page and all14 distinct unsubscripted unknowns are
preserved. The goal remains active.


## Actual numeric C222 substitution and opening accepted

The [numeric C222 substitution/opening theorem](reviews/validator-environment-substitution222-root.md)
now passes two independent builds with thirteen standard-only reports and
identical objects. Its actual Π1/IΣ1 induction retains total lookup,
repeated/zero labels and the exact qVec binder shifts. Stream selection,
semantic quantifier rules and the complete HA equivalence remain open.

The exact source replacement vector and label-matching invariant are
internal parameters. Opening inserts the interpreted free label into the
bound stack before encode_shift removes the free-environment head. Neither
step assumes a desired CProv transport theorem. The first checkpoint adds
no fresh-stream choice or arbitrary proof translation. Both remain
subsequent explicit obligations.


## Actual C222 evaluation equations accepted

The [actual C222 evaluation laws](reviews/arithmetic-command-evaluationperm222-peer.md)
now identify terminal with any stopped run and prove the exact head/tail
successor equations. Independent review and two fresh builds pass six
standard-only reports with identical objects. These supply the local laws
for the separately developed fair scheduler reach theorem.

Stopped-time uniqueness applies to the absorbing word evaluator only.
The nonzero step branch subtracts one only after its success guard.
The independent preflight corrected one implicit Init omission in a
metadata import list; the original complete closure already contained
that boundary. No source correction or compiler failure occurred.


## Source construction with actual current endpoint

The [ordinary-source construction](reviews/native-ordinary-source-construction-root.md)
now accepts every positive old-z source zero and rebuilds a Carrier65 zero
with the same scalar fields and rank. Two independent builds pass twelve
standard-only reports and identical objects. Actual current-source
existence is externally equivalent to inconsistency; shifted-z/historical
low-degree transfer and the final HA proof remain separate obligations.

These finite algebraic/number-theoretic Lean results are external. They
are not silently imported as PA/HA proof witnesses. Their later internal
coding and actual proof-existence construction remain explicitly required.


## Concrete C222 stream selection and overlap accepted

The [actual C222 stream theorem](reviews/validator-environment-streams222-root.md)
now selects an explicit safe opposite-parity stream and proves relabelling
between arbitrary free-safe starts, including overlapping s/s+2. Independent
builds pass fifteen standard-only reports with identical objects. Semantic
quantifier inference and arbitrary proof interpretation remain open.

The selector resources do not infer safety for an original unsafe stream.
Its actual formula client invokes accepted IΣ2 alpha transport; it does
not introduce a new induction or a new object-language choice rule. The
next checkpoint binds these resources and numeric substitution/opening
to actual source quantifier inference.


## Source-bound ordinary Δ₀ decisions accepted

The [actual Foundation Δ₀ theorem](reviews/foundation-ha-deltazero-root.md)
now proves HA decidability of the ordinary interpretation with arbitrary
term environments. It uses actual bounded syntax and exact binder shifts,
with twelve independently checked standard-only reports. Literal GG
comparison and the actual delta-one checker normalization remain open.

The theorem requires actual DeltaZero syntax. The consistency checker
currently has a delta-one fixed-point representation; identifying it with
an explicit bounded matrix needs further genuine HA comparison proofs.
The next separate leaf compares ordinaryAux with the literal existing
Foundation negative translation, using only these bounded decisions.


## Actual bounded negative-translation comparison accepted

The [bounded ordinary/GG comparison](reviews/foundation-ha-deltazero-gg-root.md)
now proves both HA implications for actual Foundation Δ₀ formulas and
arbitrary term environments. Two independent builds pass nine standard-only
reports. Existential recovery uses the whole bounded existential's actual
HA decision; the literal consistency-checker comparison remains open.

This comparison uses existing Foundation syntax and actual HA derivations.
The next calibration audit must bind the actual proof checker to applicable
syntax, distinguishing syntactic hierarchy witnesses from delta-one model
representations and negative consistency transport from positive Σ1 DNE.
