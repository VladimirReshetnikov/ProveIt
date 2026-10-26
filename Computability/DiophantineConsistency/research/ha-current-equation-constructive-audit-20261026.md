# HA audit of the current equation: witness routes and arithmetic proof obligations

Date: 2026-10-26. Author: `controller_certificate`.

This is a source audit, not a theorem that HA proves the equivalence. The
user's target is a Lean theorem asserting existence of an HA derivation; a
serialized derivation need not be printed. That still requires an actual
HA derivability predicate and a proof inhabiting it, rather than only a
Lean theorem about the standard natural numbers. The current accepted
external Lean equivalence and its source definitions remain unchanged.

The working checkout at the endpoint reads was
`088568987dbb2792250c67728924ce0bda115bbe`. Source hashes below identify
the principal audited inputs independently of subsequent shared commits.
No incoming script was executed, and no accepted Lean source was edited.

## 1. The target and the most useful intermediate statements

Write `Sol` for `CurrentCarrierArithmetic2011.PositiveZero
CurrentPolynomialWindow2011.polynomial` and `Ref` for the repository's
literal `BProv ZFCax_s [] Form.fBot`. `Bridge.ConZFC` is definitionally
`¬Ref`. There are three different statements to distinguish:

1. The existing external Lean theorem `¬Sol ↔ ¬Ref`.
2. A direct external witness-level equivalence `Sol ↔ Ref`.
3. A Lean theorem that the precise arithmetical sentence expressing
   `¬Sol ↔ ¬Ref` has an HA derivation.

Statement 2 gives statement 1 intuitionistically: `¬Sol → ¬Ref` maps a
refutation to a solution and contradicts `¬Sol`; the reverse implication
uses the solution-to-refutation map. No Markov principle or unrestricted
double-negation elimination is needed in this final propositional step.
But statement 2 by itself does not give statement 3. Its imported proofs
must be internalized in arithmetic, or replaced by an internal PA proof
followed by an appropriate negative-translation theorem.

The immediate external adapter can avoid the current outer classical
wrapper entirely:

```
Ref
  → DecimalMachineZFC.blank_halts_iff_zfc_refutation.mpr
  → CurrentHaltPacking2011.blank_halts_constructs_packing
  → CurrentPositiveZero2011.packingData
  → NativePositiveSourceConstruction.population_positive_polynomial_zero
  → Sol.
```

The other direction already exists as
`CurrentSoundness2011.polynomial_zero_zfc_refutation`, after opening the
positive tuple. This is the minimal next new module, provisionally named
`CurrentWitnessEquivalence2011`; it should not modify the frozen
`CurrentPositiveZero2011` closure.

In contrast, `CurrentHaltPacking2011.not_conZFC_constructs_packing` uses
`by_contra` to turn failure of consistency into an actual halt. Since
`¬ConZFC` is `¬¬Ref`, this is a genuine unbounded double-negation step.
`CurrentPositiveZero2011.no_positive_zero_iff_conZFC` also uses a classical
contradiction wrapper. Both wrappers can be bypassed in the direct
adapter. This does **not** remove classical reasoning from all its imports.

## 2. The decisive machine-calibration boundary

The current decimal machine is not justified merely by saying that it
enumerates literal ZFC proof codes. The actual endpoint passes through
the 222 calculus and a ZF/ZFC refutation equivalence.

I read the active `BusyBeaver/ZFC/KEndpoint.lean` and
`ConstructibleChoice.lean` in full. In the lower direction:

* `KEndpoint.c222_of_zf_refutation` applies
  `KEind222.c222_complete` to `DerivableNF`.
* It uses `fullSeed_direct_of_derivable`, `formSeed_of_fullSeed`, and
  `zf_consistent_of_formSeed`. The source documents a bisimulation
  quotient and its well-founded part satisfying ZF.
* `ConstructibleChoice.choice_refutation_remove` passes from a ZFC
  refutation to a ZF refutation through `completeness_inf_context`,
  a constructible submodel satisfying ZFC, and soundness.

These are valid imported external Lean results. They are not presently
an internal PA/HA proof translation supplied by the finite machine table.
Root independently audits the deeper K215 closure; this audit does not
claim to have rechecked every theorem in that closure.

Consequently, an arithmetized correctness theorem for the actual K215
endpoint is a separate, substantial obligation. A syntactic transformation
of ZFC refutations to the 222 calculus, including syntactic removal of
Choice where required, could discharge it. Another possibility is a
proved internal arithmetic reconstruction of the existing argument.
Neither follows merely from the fact that the predicates and machine
are finitely described, from an external equivalence of enumerable sets,
or from standard-only Lean axiom reports. This audit asserts neither that
such a reconstruction is impossible nor that PA already proves it.

## 3. Negative translation may avoid a complete constructive rewrite

The clarified goal permits proving existence of an HA proof rather than
extracting a literal executable witness program from every Lean proof.
A promising route is:

```
PA proves the exact arithmetic sentence Q
    → HA proves its Gödel–Gentzen translation Qᴺ
    → HA proves Q.
```

Here `Q` is the equivalence of two negative existential assertions.
Using decidable, correctly arithmetized solution and proof-verifier
predicates, HA should prove the required stability/translation identities
for these particular formulas. Those identities, the arithmetic axiom
translation, and preservation of the induction schema must actually be
proved for the chosen syntax. A truth theorem in the standard model is
not a PA derivation and cannot be fed into this route.

Repository precedents are useful but not yet this complete interface:

* `Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean` has first-order
  arithmetic terms/formulas, substitutions, six arithmetic axiom forms,
  and the full induction schema. Its existing `Prov` constructor
  `P_lem` permits arbitrary excluded middle. Thus that proof relation
  itself is classical, not HA. Formula and axiom syntax can be reused
  with a separate intuitionistic derivability relation.
* `Logic/Propositional/NaturalDeduction/Lean/NaturalDeduction/Calculus.lean`
  distinguishes intuitionistic and classical propositional derivations,
  but supplies neither first-order quantifiers nor arithmetic induction.
* The existing Coq file
  `Logic/FoundationPort/Coq/FirstOrder/NegationTranslation/GoedelGentzen.v`
  defines `ifo_double_negation_translation` and culminates in
  `ifo_goedel_gentzen_provable`. It translates classical first-order
  theoremhood to an inhabited intuitionistic proof of the translation.
  The source also has substitution/rewriting compatibility. The final
  theorem does not itself instantiate HA/PA axioms or induction. I read
  its translation definition and final theorem; the separate circuit
  agent inspected the full proof-system interface. No Coq proof was run
  in this audit, and no Lean HA instantiation is claimed from that file.
* The list-coding development already treats sequence, finite sum,
  finite product, and power relations. Reusing syntax or an external
  satisfaction theorem does not automatically give an HA proof of
  totality and correctness of those relations.

The parallel `HAProofs` work is owned by another agent. This audit does
not duplicate it or assume that its eventual logical infrastructure
settles the arithmetic or machine-calibration obligations.

## 4. Native arithmetic: finite replacements and concrete bounds

The following are candidate arithmetic reconstructions supported by the
read source, not newly formalized HA proofs.

| Current source/use | Constructive arithmetic replacement or obligation |
| --- | --- |
| `CurrentMarkedWindow2011.assignment` uses `Classical.choose` on occupied cells. | Search the 942 physical selectors in a fixed cell. The decoded one-hot property supplies existence and uniqueness. This is a finite search, not countable choice. |
| `WangTiles942Soundness.marked_halts_before_period` argues by contradiction. | It concludes a halt at a time `t < N`. Decide the finite list of run states at `0,…,N−1`; the no-halt branch is refuted by the existing row induction and periodic Start-north color 435. No unbounded Markov step is necessary. |
| `NativeCyclicCarry.exists_bounded_carries` uses `OrderHom.lfp` for arbitrary index type. | In the actual finite word, start all carries at zero and iterate the monotone quotient update. The sum of carries is at most `57*(2011*N)`. Every nonstationary monotone step increases that sum, so a fixed point is reached within that many strict steps. A formal finite-iteration proof should replace the arbitrary-lattice construction for arithmetic internalization. |
| `ControllerPowerCoordinates.exists_coordinates` chooses coordinates and uses `Equiv.ofBijective`/finite surjectivity. | Enumerate the finite orbit and select the least coordinate below its known modulus. Invert the resulting permutation by bounded search. The already proved exact finite order supplies the necessary uniqueness and coverage. |
| Unit inverses and residue-lift subsets. | Extended Euclid or search below the modulus supplies inverses. `ControllerIntervalSums.startFor` and interval subsets are already explicit finite arithmetic once the inverse is fixed. |
| Finite dummy mutation, rank decrement, population and parity. | All updates are indexed by explicit finite supports and use exact ordinary integer equalities. The target support has cardinality at most `d*auxiliary`; its indices lie below `N`. Encoding the lists, folds and congruences remains work. |
| Fixed table, permutation, kernel, masks and prime certificates. | These are finite constants/identities and can be checked arithmetically. Their current closed Lean proofs still need a proof-producing arithmetic reflection or explicit HA/PA derivations; external Python receipts are not proof premises. |

The carry replacement is especially local: retain the current raw budget
and quotient formula, specialize the index type to a finite list, and
prove stabilization by an integer sum potential. It needs no tile,
controller, or consistency assumption. For the empty finite type the
initial vector is already fixed; actual words have positive length.
This would be the smallest substantive new constructive arithmetic
module after the direct witness adapter.

The reverse geometric dimensions are already given explicit witnesses.
For a halt at time `T`, `exists_power_dimensions` chooses
`rw = 2*T+wBound+5`, `rh = T+hBound+5`. The controller specialization
replaces the requested height bound by `max hBound (auxiliary^2)` and
sets `k = rw+rh−1`, `N = auxiliary^(k+1)`. No unbounded search for a
large prime, width, or height occurs: the auxiliary prime is fixed.
The tableau is obtained from the finite actual run through time `T`.
The size is enormous but explicit.

The controller then builds the new rank from ordinary polynomial/word
quantities, proves its parity, and rephases the same finite word at
`t = (R−width*N)/d`. Its multiplier is the explicit power
`2^(R−width*N)`. An internal proof must establish totality of these
operations and their coded finite sequences; this audit does not claim
a formal global primitive-recursive witness bound has already been
proved for the complete refutation-to-solution chain.

## 5. Pell arithmetic and fresh witnesses

`NativePositiveSourceConstruction` directly consumes the constructed
packing scalars and the population identity. It constructs a canonical
parent and restores the fourteen positive coordinates. The relevant
number-theoretic witness obligations are identifiable:

* `NativeOuterSeedConstruction` defines the outer powers and Pell indices
  from `R` and its half-index, with exact quotients justified by
  divisibility. The half-binomial floor has a finite binomial expansion.
  Exact divisible quotients can be defined using natural division;
  existential divisibility elimination need not be an unbounded search.
* `ThirteenFreshSeed.auxiliary_exists` needs a positive index at which
  a prescribed `m = b*c^2` divides a Pell `yn` value. The current
  `Diophantine.exists_dvd_yn` invokes
  `Finite.exists_ne_map_eq_of_infinite` on the pair of Pell residues
  modulo `m`. There are exactly `m^2` residue pairs. The same argument
  applied to indices `0,…,m^2` gives a positive difference at most
  `m^2`; the existing subtraction identity then proves divisibility.
  A bounded version, followed by bounded search, is sufficient. This
  finite bound has been derived here from the read proof, not added as
  a new checked theorem.
* Pell sequences are given by integer/natural recurrences. Their
  finite evaluations and growth comparisons can be represented by
  coded sequences and induction. No need to search for an arbitrary
  fundamental Pell unit arises in the inspected first-norm route:
  `NativePellBootstrap.firstUnit` is the explicit solution `(2Q+1,2)`.
* Mathlib's `IsFundamental.eq_pow_of_nonneg`, actually invoked by
  `first_norm_classification`, uses strong induction on the positive
  integer `x` coordinate. Its descent multiplies by the inverse of the
  supplied fundamental solution and strictly decreases that coordinate.
  This is a finite descent, not a real-analysis existence proof.
* `NativeOuterSeedConstruction.pell_interval` and
  `Diophantine/Paper1980/PellRatio90.lean` currently use inequalities in
  `ℝ`, with reciprocal positive integer expressions and finite powers.
  The inspected upper/lower-estimate proofs are algebraic inequalities
  and induction/Bernoulli estimates; they do not invoke a limiting
  analytic existence principle. For direct HA/PA internalization, replace
  these statements by denominator-cleared integer inequalities (or prove
  a sound coded-rational interpretation). Merely importing `ℝ` theorems
  is not a proof of their arithmetic formalizability.

The soundness-side signed step-down, Pell classification, population
and binary-power extraction also require arithmetical versions of their
sequence and modular lemmas. Their `by_contra` uses on explicitly
decidable integer inequalities are not in themselves an HA obstruction.
This audit has not proved that every transitive Pell dependency admits
a uniform translation with a stated induction bound.

## 6. Representation, induction and the precise remaining claim

For the solution side, strictly positive integer variables can be
represented by natural variables `v_i = n_i+1`, and integer polynomial
equality by equality of natural positive/negative parts. The fixed large
ports are numerals (or conservative, fully defined arithmetic
abbreviations). No variable exponent remains in the final Diophantine
polynomial. Powers, sequence evaluation, finite sets and coded traces
belong to the proof of its correctness and need appropriate arithmetic
graph formulas and proofs of totality.

HA has induction for every formula; the present task does not require
quantifier-free induction alone. The finite algorithms and Pell
recurrences suggest primitive-recursive coding interfaces, but it would
be unjustified to announce a quantifier-free-induction proof or a
particular weak-arithmetic bound without proving the representation and
induction translations. Exponentiation is not a primitive symbol of
the bare `0,S,+,*` language and its graph/totality must be accounted for.

For the refutation side, the actual set-theoretic syntax, axiom schema
and derivations need a natural-number checker with correctness proved
against `BProv ZFCax_s [] Form.fBot`. The arithmetic `RefCode` formula
must denote that exact predicate. A generic classical proof relation
or a different proof checker is not a substitute without a proved
translation. Root's active K-endpoint audit is central here.

A sensible sequence of next checkpoints is therefore:

1. Add the direct external `CurrentWitnessEquivalence2011`, explicitly
   retaining the imported K endpoint's scope. This removes the avoidable
   outer DNE while preserving the exact polynomial and refutation.
2. Define HA derivability on the existing arithmetic syntax; establish
   the specific negative-translation/stability interface and axiom plus
   induction preservation. This is owned by the parallel logic task.
3. Prove internal PA or HA arithmetic correctness of the native/Pell
   transformations using finite carry iteration, bounded Pell residue
   repetition and coded recurrences. A PA route avoids requiring every
   existing proof to be rewritten constructively.
4. Supply an internal arithmetic calibration for the actual K215/ZFC
   endpoint, including the lower 222-calculus and Choice-transfer
   obligations. This is not supplied by steps 1–3.
5. Compose the resulting derivations for the exact closed sentence and
   transfer the already checked positive-variable algebraic frontiers
   inside the same proof system.

The audit supports this plan; it does not conclude HA provability yet.
The corrected thirteen-variable and other arithmetic equivalences add
finite algebraic obligations, not a replacement for the machine and
proof-system calibration.

## 7. Read scope and provenance

The principal endpoint, packing/source construction, carry, controller
coordinate/interval, dimension, fresh-seed and first-order/propositional
definitions described above were read directly. In very large files
(`PASyntax`, `PellRatio90`, Mathlib `Pell`) the cited definitions and
relevant proofs were read, rather than the entire file. The full active
machine closure and Coq GG development were not independently replayed.
The earlier accepted Lean builds remain their own evidence; this audit
ran no new Lean proof and is not a closure rebuild receipt.

The author implemented several native prerequisites, including literal
kernel/window binding, cell/word construction, scalar witnesses, units,
dummy safety/mutation, labels, translation and row step. This is an
implementation-informed audit of those dependencies, not an independent
peer certification of the whole original equivalence. Root separately
reviewed the lower machine calibration; the circuit agent identified the
Coq GG precedents and owns the new intuitionistic arithmetic calculus.

Exact source bindings follow.

| Source (repository-relative) | SHA-256 |
| --- | --- |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPositiveZero2011.lean` | `cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentHaltPacking2011.lean` | `6ed64c4b270ba07ababf8412dfad7ea8d69d7fbcd005f7f403f65fd34b4ead4f` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSoundness2011.lean` | `1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/DecimalMachineZFC.lean` | `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` | `04965b2e82b0f22cdbb11910c17ddf82efafe26123040d6b1b01a88707ec8175` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` | `3728efadefd93d944836c0f70d18aabbad37274b8c474594b8f01b89dd0eb84c` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeCyclicCarry.lean` | `25c08e2b6b10e72fe9b3d4df81078e4e1e5ede8e3e94b9666dc5616dcfebc72e` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePositiveSourceConstruction.lean` | `f96ba070ef8dac85ea4d63cf687efbee7b9f75f65e35ef498c9c028551bacf5d` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean` | `fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenFreshSeed.lean` | `6312b55f52b22306d2f070920bfc1b3002d397ae171b9dbcc9df828087781992` |
| `Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean` | `1ba5f0223a6099751c06e37079e717e463cd40cf8ec092ac95647383c7ffb623` |
| `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRatio90.lean` | `5b790da2863fba41ac42b56675c77bc8404a2e5834e9a44ab255602e5a3fbbd0` |
| `.lake/packages/mathlib/Mathlib/NumberTheory/Pell.lean` | `5f38f09819987553a211f03819fcc542d26abd920642dddbb935a9b72d05936c` |
| `Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean` | `1c2a64fc5cd25092287a94af33c6ea4ce7815615965aa35c1c6fce6e18206b37` |
| `Logic/Propositional/NaturalDeduction/Lean/NaturalDeduction/Calculus.lean` | `95adb3c2e49d001f2ae20abb08375ade86ad695e14f928754e82a81162660871` |
| `Logic/FoundationPort/Coq/FirstOrder/NegationTranslation/GoedelGentzen.v` | `cbaca0de5b793f34b92bc3baa24c3a8cfd9a30e65baabfd1e7e3687a3d01a521` |

## 8. Same-day reuse addendum after the user's repository pointers

The user's additional pointers exposed substantially more existing internal
arithmetic machinery. This narrows the work proposed above: **do not rebuild
internal Choice removal, the numerical validator, or the Rotation240 PA
endpoint from scratch.** The unresolved comparison is with the actual
current215 machine/calculus and current equation.

I read the full active sources of
`ZFCinPA.ValidatorConsistencyEquivalence`,
`ZFCinPA.RotationInterpreterConsistency240`, and
`ZFCinPA.BinaryConsistencyRotation240`. These are real object-arithmetic
provability statements. In particular:

* `ValidatorConsistencyEquivalence.peano_proves_con_ZFC_iff_validator`
  proves in PA that Foundation's coded ZFC consistency sentence equals
  absence of an internal code with `ArithmeticHistory254.value code = 2`.
  The stronger source theorem uses IΣ₂.
* Its imported `LSchema` already supplies internal Choice transport.
  The actual source exports `iSigma1_proves_con_ZF_imp_con_ZFC` and
  `peano_proves_con_ZF_iff_con_ZFC`. Root is independently inspecting
  that proof/calibration; this addendum does not claim a new replay.
* `BinaryConsistencyRotation240.peano_proves_con_ZFC_iff_not_binary_halts`
  proves the exact binary Rotation240 nonhalting equivalence in PA.
  `isigma1_proves_blank_iff_rotation_halts` identifies its binary and
  register-interpreter sentences at arbitrary internal times, and the
  consistency composition is in IΣ₂.

Use of external classical completeness in these proofs is legitimate for
the requested *existence of a PA proof*: their premises are theorems in
every appropriate arithmetic model, including nonstandard models, and
their conclusions inhabit the actual arithmetic provability predicate.
This is quite different from feeding a theorem about ordinary `Nat` into
completeness. A subsequent GG theorem can operate on this provability
result without printing a serialized PA proof.

The user specifically identified
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215`.
I read its root README (82 lines), Lean README (88), independent-audit
README (25), and simplification index (104), together with the relevant
part of the nested `k215-simplification-2/proof_audit/audit.md`. All
explicitly separate the checked external215 endpoint from an internal
PA proof; the nested audit explicitly contrasts it with the completed
Rotation240 PA theorem. The many nested proposals and saved closures
are not new arithmetic derivations merely because their kernel checks
are complete. No proposal driver, compiler wrapper, or incoming script
was executed here.

Scoped text searches over the active
`BusyBeaver/ZFC/Arithmetic*.lean` and `ZFCinPA/*.lean` found no reference
to `KCode222`, `C222`, `EnumPerm`, `DagPerm`, `KSource215`, or `KDense215`.
Searches for internal provability/theory markers in the named k215
proposal Lean/Rocq sources found no current215 internal endpoint. This
is evidence about the searched sources, not a proof that no reusable
lemma exists anywhere in the large repository.

The actual differences prevent an immediate endpoint rewrite:

* `SeedPerm` sets the215 candidate counter to `4` and other source
  registers to zero. Its `dagPerm_seed_iff` is an external equivalence
  with `KCode222.C222 Code254.F`.
* `KSource215.p215_halts_iff` is a checked external normalized
  register-program bisimulation with `pathDagPerm`, for every ordinary
  register file. It is not yet stated for arbitrary internal arithmetic
  registers or represented runs.
* The Rotation240 arithmetic source uses the seed
  `⟨3,0,0,0,3,0,0,0,0⟩`, an interpreter compared with `Dag254`, and the
  twelve-row `Code254History` validator.
* `KCode222` explicitly changes the equality row to `growG` and the
  gated bundle to the helper-free seed bundle. Its endpoint cannot be
  identified with the old validator by silently treating these as the
  same calculus.
* The PA theorem's consistency sentence is Foundation's internally coded
  theory `𝗭𝗙𝗖`. Its exact relation to the existing external
  `BProv ZFCax_s [] Form.fBot` must retain the repository's supplied
  theory/coding translations. Neither identical typography nor the
  standard-model agreement alone is an internal proof comparison.

There is useful generic infrastructure for a missing exact215 arithmetic
bridge: `ArithmeticMachineGraphPerm252` has a literal-table lookup
compiler; the Rotation240 graph is a short instantiation of it.
`ArithmeticPositiveSimulation254.halts_iff` works in arbitrary IΣ₁
models with represented runs, a Σ₁ relation and positive-clock simulation
contracts. It retains those concrete contracts as hypotheses, so they
must be proved for the215 boot, source and changed calculus. Reusing this
framework is preferable to restating only the current external simulation.
A direct internal calibration of the changed C222 validator, or an
internal comparison to the existing254 validator, would then connect
to the already proved ZFC consistency endpoint.

The circuit agent also located the original Lean GG implementation in
the external Foundation source checkout:
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/NegationTranslation/GoedelGentzen.lean`.
I subsequently read all 199 lines. It contains the recursive
`Derivation.gödelGentzen`, `Provable.gödel_gentzen`, substitution
compatibility, and `Theory.ToTheoryᵢ`. This improves on the initial
Coq-only inventory. It still needs arithmetic-theory/induction
instantiation and the exact target stability bridge. That checkout uses
a different pinned toolchain; none of its objects were loaded or
executed by this audit.

Finally, the authorized direct adapter is now a separate frozen packet:
`CurrentWitnessEquivalence2011` and its checks both passed fresh bounded
Lean builds. Its author receipt is
`reviews/current-witness-equivalence2011-author.md`. This closes the
external direct witness interface identified in section 1, while leaving
the internal-PA/HA obligations and reuse opportunities above explicit.

Additional source bindings:

| Source | SHA-256 |
| --- | --- |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorConsistencyEquivalence.lean` | `e0502e78a7c1a4a8c6d3f242279ae557ce91678dfd9cb52aa628bf38c0fbd242` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/RotationInterpreterConsistency240.lean` | `a07acc1fc3b84aa55281f9fa590246b365353867157e54c5a027436d19e777b1` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/BinaryConsistencyRotation240.lean` | `e045e91d01a61857bee0852fa50c16399ca89130c05c6b5be2e2ca15750d08fa` |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` | `06b24aaaa63ba4f0826d2f6eb08d30bcfdbf12e1ba871382b540538b0e3b965b` |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/README.md` | `5a0d18caab365cff70b735f9256e21ce8fb0992ad6ef31044405b75c69dbcad3` |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/independent-audit/README.md` | `37b8cc4efb5479874aad4fd1f3cb2c6ff96dcac35b4597cd6c383556e12aec1f` |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/README.md` | `574591a7eb2f3c8085422e4b6094cb7a21a01f6652674080cd1fdfff0e3e7e83` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SeedPerm.lean` | `ed038b38122aca4ebd1f31a48f2ea9e99d2bb6f33a406cab4039ba62163b80ec` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215.lean` | `1a25e38fa662a609357d41eb307ee7156ec55c1502cc3298c5556ab1f20bb245` |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticPositiveSimulation254.lean` | `ec9c249013345061fb2dd99b1cb387f10dfd5d69447100465ff2b7558e949290` |
| External Foundation GG source at the absolute path above | `52fabd00a01e1f5671e1f078c36f9848f2e219e0a4e616deaad4e523057586ea` |
