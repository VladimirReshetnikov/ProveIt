# Negative Σ₁ calibration after bounded GG comparison

This is a read-only proposal, 2026-10-26. No new Lean theorem is claimed here,
and no source or object was changed or compiled for this audit. The exact
source and existing-cache pins are in
`ha-negative-sigma-one-calibration-pins.json` beside this note.

## Finding

The existing Δ₀ comparison does **not** directly normalize the actual
Foundation proof checker. Its `proof` is a pair of Σ₁/Π₁ formulas, and the
Σ₁ half contains unbounded graph/fixedpoint witnesses. Nevertheless, a more
general, constructive **negative** comparison appears to avoid any need to
extract or code those witnesses: prove, for the actual syntactic class
`Hierarchy Σ 1 p`,

```
HA ⊢ GG(p) ↔ ¬¬ordinary(p),
```

then take negations. The substantive additional ingredient is finite bounded
double-negation shift, proved by HA formula induction. It is not unbounded
double-negation shift, Markov's principle, or positive Σ₁ double-negation
elimination. The fixed-source specialization would compare the already fixed
`ggConsistency` with the **HA negation of the ordinary interpretation of the
exact source `provabilityPred ZFC ⊥`**. It would not identify an independently
chosen bounded checker, an executable validator, or PAHF `BProv` internally.

## Exact source chain and hierarchy evidence

Paths beginning `Foundation/` below are relative to the pinned vendor root
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/`.

* `Foundation/FirstOrder/Incompleteness/Consistency.lean:36` defines
  `Theory.consistent : Π₁.Sentence` as
  `.mkPi (∼provabilityPred T ⊥)`. `mkPi` retains that exact formula; it is
  not a prenex compiler. `consistent.defined` at line 39 is model semantics.
* `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean:461–490`
  defines `derivation`, `derivationOf`, `proof`, `provable`,
  `provabilityPred`, and `provabilityPred'`. In particular:
  `proof.sigma` is `∃s, insertDef s φ 0 ∧ derivationOf.sigma d s`;
  `provable` is `∃d, proof.sigma d φ`; `provabilityPred` substitutes the
  literal quotation; and `provabilityPred'_val` proves the typed Σ₁ wrapper
  has exactly that same value. Thus
  `(provabilityPred' T ⊥).sigma_prop`, rewritten by that equality, supplies
  **actual syntactic `Hierarchy Σ 1` evidence** for the desired predicate.
* `Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean:36–41` defines the
  fixedpoint Σ₁ formula and its Δ₁ pair. The latter's Σ half is
  `∃L, limSeqDef L (x+1) … ∧ x∈L`. `limSeqDef` uses the PR blueprint's
  `resultDef`. `HFS/PRF.lean:22–33` includes an unbounded sequence witness
  and bounded checks containing the supplied Σ₁ step graphs. The exact
  source is therefore not merely `∃d, D₀(d)` with a given Δ₀ proof matrix.
* `Arithmetic/Definability/Hierarchy.lean:55–107` defines `mkSigma`,
  `mkPi`, `mkDelta`, `val`, `sigma_prop`, and `pi_prop`. `mkDelta` stores
  two formulas; it does **not** store a syntactic Δ₀ formula or even their
  equivalence. `ProperOn` at line 132 is equality of evaluations in a
  specified structure. `ProvablyProperOn` at line 138 is a **classical
  Foundation theory proof** of their closed equivalence. Its
  `ofProperOn` construction at line 168 invokes classical completeness.
* `Bootstrapping/Syntax/Theory.lean:13–17` specifies `Theory.Δ₁` by a
  characteristic pair, standard-Nat membership on quotations, and an
  `IΣ₁` proof of properness. The exact ZFC instance is the union of the
  instances in `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ZFDelta1.lean`.
  None of these properness fields is an HA decision theorem for the matrix.

The fixed target is already named in
`Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean`:
`sourceSentence` is this actual Foundation ZFC consistency sentence, and
`ggConsistency := FoundationPAHFSyntax.sentence sourceSentenceᴺ`.
Its standard-Nat theorem uses the explicit existing C254/ZF/ZFC convention
chain and concludes the negation of
`SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot`.
That semantic theorem remains distinct from a proof of an HA equivalence.

`FoundationHAZFCValidator.lean` already supplies closed HA implications
between `ggConsistency` and the GG image of the actual C254 validator
consistency sentence, using the concrete closed PA equivalence. Here too the
validator's acceptance formula uses `ArithmeticHistory254.valueDef`, an
actual Σ₁ graph (`BusyBeaver/ZFC/ArithmeticHistory254.lean:121`), not a
claimed Δ₀ matrix. These are C254 conventions, not a 215/222 runtime bridge.

## What pure negative-existential transport does and does not cover

For an actual Δ₀ matrix `p`, the accepted `ordinary_gg_equivalence` gives
both HA directions at every capture-safe term environment. Standard
intuitionistic quantifier rules then compare
`¬∃x ordinary(p)` with `¬GG(∃x p)` without deciding an unbounded existential.
A finite unbounded existential prefix can be handled similarly.

This prenex special case is insufficient **as a literal match** for the
current fixedpoint source. The inspected source contains bounded universal
checks of Σ₁ graph formulas. A search over the current Foundation
`FirstOrder/` and `Syntax/Predicate/` sources found no reusable prenex or
Δ₀-matrix-normalization API; the typed hierarchy wrappers do not perform
normalization. This is a scoped search result, not a claim that no alternative
coding theorem could be developed.

A separate HA witness/coding normalization would be needed if the target
were an independently specified proof-code/decidable-matrix checker. It
appears unnecessary for the narrower target which retains the **same actual
positive Σ₁ source formula** and places HA negation outside its ordinary
interpretation. The following hierarchy route addresses precisely that target.

## Smallest recommended first implementation

New `HABoundedDoubleNegation.lean` and focused checks, importing only the
frozen `HABoundedQuantifiers`. Use its literal `ball`, `inst`, `plus`, and
`HANegativeStability.doubleNeg`. Proposed genuine object-proof endpoints:

```
bounded_doubleNeg_shift (t : Term) (a : Formula) :
  HA.Proves (.imp (ball t (doubleNeg a)) (doubleNeg (ball t a)))

bounded_doubleNeg_forward (t : Term) (a : Formula) :
  HA.Proves (.imp (doubleNeg (ball t a)) (ball t (doubleNeg a)))
```

No decision, syntactic class, semantic correctness, or standard-witness
premise is imposed on `a`. Finite `Relative Ax_s G` versions follow by
weakening the resulting theorems. The proof uses actual HA induction on

```
ball (var 0) (doubleNeg (plus a)) →
  doubleNeg (ball (var 0) (plus a)).
```

The base follows from `ball_zero`. The successor decomposes
`ball (S t) a` into `ball t a ∧ inst a t`, using the two accepted
`ball_succ_*` laws, the induction hypothesis, and the intuitionistic finite
law `¬¬A ∧ ¬¬B → ¬¬(A∧B)`. Capture-safe instantiation and successor identities
must retain all ambient parameters, just as `decisionBody_inst/succ` do in
the parent. Tests should include empty and successor intervals, sparse free
indices, nested binders, shifted finite contexts, and an arbitrary undecided
matrix. Expected size: roughly 130–200 main lines plus focused checks.

This is finite DNS for a syntactically bounded quantifier. It supplies neither
`∀x¬¬A(x) → ¬¬∀xA(x)` nor `¬¬∃xA(x) → ∃xA(x)`.

## Subsequent actual Σ₁ and fixed-source endpoints (not implemented)

Use the actual existing eight-constructor Foundation syntax and actual
`Hierarchy Σ 1`; do not define a competing checker grammar or GG algorithm.
For arbitrary environments, the exact next target is:

```
sigma_one_doubleNeg {p : Semiformula ℒₒᵣ ξ n}
    (hp : Arithmetic.Hierarchy Σ 1 p)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
  HA.Proves (.and
    (.imp (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)))
    (.imp (doubleNeg (ordinaryAux bv fv p)) (formulaAux bv fv pᴺ)))
```

`Hierarchy` is defined in `Arithmetic/Basic/Hierarchy.lean:10–26`. At Σ1,
the admissible cases are literals/constants, conjunction/disjunction,
positive-bounded all/ex, unbounded existential, and a Σ introduction over
Π0. Unbounded universal and the dummy alternation constructors cannot occur
at this polarity/level. The Π0 base is Δ₀ by `zero_iff_delta_zero`.

Conjunction uses finite double-negation pairing. Disjunction and existential
retain their existing GG negative encodings; only double-negated ordinary
formulas are recovered. For bounded all, exact positive-bound extraction
and order-atom decidability convert the guard to `L→…`; use finite DNS on
the ordinary matrix. For bounded existential, retain the outer double
negation. In particular, do **not** assert
`¬¬bex t a → bex t (¬¬a)` for arbitrary `a`: it would demand a finite choice
of a disjunct that the proposed proof does not supply.

For a closed source `ρ`, reuse Foundation's existing
`Derivation.neg_doubleNegation`, already transported to actual HA by
`FoundationHACurrentTransfer.translated_neg`. Combining its proof with the
Σ₁ comparison gives `sentence (∼ρ)ᴺ ↔ neg (ordinarySentence ρ)`.
`ordinarySentence` can be just `ordinaryAux Fin.elim0 Empty.elim`; a small
structural embedding equality relates it to the canonical `sentence` wrapper.

The fixed final specialization would take exactly
`ρ = provabilityPred (ZermeloFraenkelChoice : SetTheory) ⊥` and return both HA
implications between `FoundationZFCConsistencyNat.ggConsistency` and
`neg (ordinarySentence ρ)`. Its syntactic premise is discharged by the
existing typed predicate and exact substitution identity, not by a new
desired-equivalence hypothesis or by `ProperOn`.

Do not silently replace this target with `ordinarySentence (∼ρ)`.
Foundation NNF negation distributes through conjunction and bounded
universality; its ordinary interpretation can introduce disjunctions or
existential alternatives. General intuitionistic De Morgan reversal is not
available. Nor does the proposed theorem identify the fixed source predicate
with an independently encoded PAHF proof relation inside HA. Those remain
separate representation/calibration obligations. The current-equation PA
equivalence and the actual 215/222 internal runtime bridge also remain open.

## Cache boundary and execution status

The first finite-DNS leaf needs exactly **101 cached modules, 76 Foundation,
329 existing artifacts, 34 explicit external boundaries**, by traversal from
`HABoundedQuantifiers` in the authenticated GG-parent manifest. Its selected
root parent is `/tmp/ha-bounded-quantifiers-root-peer-gtq42hal/lib`, main
object `5aef4873ce228ef55ac107f2fb0c251da951552feee7d0acb92f0ca3061a992f`.
Only the new main/check pair would be fresh; no Foundation build is needed.
The JSON records a read-only rehash of every selected source/object and
external boundary, not a new compiler replay or a full package audit.

For the later generic Σ₁ leaf, the frozen GG-parent 102 modules plus its new
GG main is a 103-module baseline; the future finite-DNS main would make 104.
The existing fixed-target HA manifest (448 modules) union this 103-module
GG baseline has **453** existing modules with no common source-pin conflict:
the five additions are OrderDecidable, StrictIntervals, BoundedQuantifiers,
DeltaZero, and DeltaZeroGG. Future DNS/Σ₁ leaves would add two modules. This
is a read-only count, not approval or execution of a fixed-target build.
Root's independent GG replay is still the authoritative acceptance step.
