import ZFCinPA.SubstIdentity
import ZFCinPA.StagedSuccessor

/-!
# The shared source layer of the certificate-field successors

`ZFCinPA.LocalStepSuccessor` established the compilation route for the
first certificate field: at an arbitrary model index `x : V` every field
code of `ZFCinPA.CertificateFields` is a fixed constructor spine over
exactly **two** `x`-dependent leaves, `numChainCode x` (unary) and
`closCode x` (binary), so it is the specialization at
`levelLeaves x = ![numChainCode x, closCode x]` of a fixed source formula
over the placeholder language `setTemplateLanguage 2 ![1, 2]`.

That observation is *field-independent*.  This module therefore carries
the whole apparatus that all five fields share, so that the per-field work
is only the field's own source spine and its source proof:

* **Shift-fixedness of the two leaves** (`shift_numChainCode`,
  `shift_closCode`, `shift_levelLeaves`).  This is the hypothesis
  `SetPlaceholders.compileSetTemplate` places on *any* interpretation of
  the placeholders, so it is needed once, by every field.  Both proofs are
  model-internal `𝚺₁` successor inductions along the `PR` towers of
  `ZFCinPA.LevelCodeTower`, in the pattern of
  `ConcreteFamily.isSemiformula_numChainCode`/`isSemiformula_closCode`;
  the bookkeeping is packaged in the auxiliary predicate `ShiftFixed`,
  whose introduction rules bundle well-formedness with the shift equation
  so the nineteen-leaf closure-step spine is discharged by one
  `repeat' first | …` in exactly the shape `isSemiformula_closCode` uses.
* **The template and its atoms** (`levelArities`, `srcL`, `levelLeaves`,
  `srcPProp`, `srcPlaceholder`, `liftP`) with their reconciliation lemmas.
* **The source level tower at the canonical slots** (`srcLevelSat`,
  `srcSigmaTrue`, `srcPiFalse`, `srcPiTrue`, `srcCanonAt`).
* **The source counterpart of the two towers' successor steps**
  (`srcNumChainSucc`, `srcClosStep` and its four layers).  This is the
  piece every field's successor needs and none of them can avoid:
  `closCode (x+1) = closStepCode (numChainCode x) (closCode x)` is a
  nineteen-leaf spine, and each field's successor formula has to unfold
  the next level's closure exactly this way.  It is written once, at an
  arbitrary ambient arity, with a depth move per fixed leaf.

`ZFCinPA.LocalStepSuccessor` imports this module and re-exports its
contents, so nothing downstream sees the split.

## Disciplines

The parameter firewall of `ZFCinPA.LevelCodeTower` is respected
throughout: concrete Gödel constants are touched only through
`coe_toNat_eq_quote` and the depth-move lemma `quote_toSet_eq_code`, and
they are made `local irreducible` before the spine tactics run, so no
`simp` or unification step can ever try to evaluate one.  Every free-slot
bound is either a named lemma of `ZFCinPA.LevelCodeTower` (`fm01`–`fm16`,
`freeMax_closF_zero` — each a ~1M-heartbeat kernel evaluation, exported
there precisely so that it is performed once in the whole project) or a
two-line consequence of one.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LeanProofs
namespace ZFCinPA
namespace SuccessorSources

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SubstIdentity
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF fIsFormCodeF
  fTaggedEmptyF fTagUnF fPiBoundedF fSigmaBoundedF fShiftTripleMemF
  fLevelImpF fLevelAndF fLevelOrF)

/-! ## Shift-fixedness, as a bundled invariant

`Bootstrapping.shift` raises free-variable indices; the raw constructor
equations for it carry `IsUFormula` side conditions.  Bundling
well-formedness with the shift equation turns those side conditions into
part of the invariant, so the spine walk below is a pure application of
introduction rules. -/

section ShiftFixed

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A code that is a well-formed `ℒₛₑₜ` formula and is fixed by the
internal `shift`. -/
def ShiftFixed (p : V) : Prop :=
  IsUFormula ℒₛₑₜ p ∧ Bootstrapping.shift ℒₛₑₜ p = p

theorem ShiftFixed.and {p q : V} (hp : ShiftFixed p) (hq : ShiftFixed q) :
    ShiftFixed (p ^⋏ q) :=
  ⟨IsUFormula.and.mpr ⟨hp.1, hq.1⟩, by
    rw [Bootstrapping.shift_and hp.1 hq.1, hp.2, hq.2]⟩

theorem ShiftFixed.or {p q : V} (hp : ShiftFixed p) (hq : ShiftFixed q) :
    ShiftFixed (p ^⋎ q) :=
  ⟨IsUFormula.or.mpr ⟨hp.1, hq.1⟩, by
    rw [Bootstrapping.shift_or hp.1 hq.1, hp.2, hq.2]⟩

theorem ShiftFixed.all {p : V} (hp : ShiftFixed p) : ShiftFixed (^∀ p) :=
  ⟨IsUFormula.all.mpr hp.1, by rw [Bootstrapping.shift_all hp.1, hp.2]⟩

theorem ShiftFixed.exs {p : V} (hp : ShiftFixed p) : ShiftFixed (^∃ p) :=
  ⟨IsUFormula.ex.mpr hp.1, by rw [Bootstrapping.shift_exs hp.1, hp.2]⟩

theorem ShiftFixed.imp {p q : V} (hp : ShiftFixed p) (hq : ShiftFixed q) :
    ShiftFixed (Bootstrapping.imp ℒₛₑₜ p q) := by
  refine ⟨?_, ?_⟩
  · simp only [Bootstrapping.imp]
    exact IsUFormula.or.mpr ⟨hp.1.neg, hq.1⟩
  · simp only [Bootstrapping.imp]
    rw [Bootstrapping.shift_or hp.1.neg hq.1,
      Bootstrapping.shift_neg hp.1.isSemiformula, hp.2, hq.2]

/-- A named standard code is well-formed at its own translation depth.
(Local copy of the `ConcreteFamily` helper, which is private there.) -/
theorem leafIsSemiformula {k : ℕ} (φ : SetTheorySemiproposition k) :
    IsSemiformula ℒₛₑₜ ((k : ℕ) : V) ((φ.toNat : ℕ) : V) := by
  rw [coe_toNat_eq_quote]
  simp

/-- **A fixed leaf is shift-fixed.**  A `toSet`-translation whose free
slots all lie below the declared depth has no free variables, so the
*metatheoretic* shift fixes it, and `Semiformula.quote_shift` transports
that to the internal `shift`. -/
theorem shiftFixed_leafCode {φ : SetTheory.Form} {k : ℕ}
    (h : ∀ i, SetTheory.Free i φ → i < k) :
    ShiftFixed (((toSet k φ).toNat : ℕ) : V) := by
  have hs : Rewriting.shift (toSet k φ) = toSet k φ := by
    refine FirstOrder.Semiformula.rew_eq_self_of (by simp) ?_
    intro x hx
    rw [FirstOrder.Semiformula.FVar?, freeVariables_toSet φ k h] at hx
    simp at hx
  refine ⟨(leafIsSemiformula (V := V) (toSet k φ)).isUFormula, ?_⟩
  rw [coe_toNat_eq_quote, ← FirstOrder.Semiformula.quote_shift, hs]

end ShiftFixed

/-! ## Free-slot bounds of the fixed leaves

Each bound is `free_lt_freeMax` against one of the exported kernel
evaluations of `ZFCinPA.LevelCodeTower`; the two compound leaves
(`numPairF`, the two witness records) are one `freeMax` unfolding on top
of that.  Nothing here re-`decide`s a bound. -/

section FreeBounds

open SetTheory (Form Free)

theorem free_tripleMemHead {i : ℕ} (h : Free i (fTripleMemF 2 1 0 4)) :
    i < 5 := by
  have := free_lt_freeMax _ i h; have := fm01; omega

theorem free_univEnvLeaf {i : ℕ} (h : Free i (fUnivEnvF 1)) : i < 5 := by
  have := free_lt_freeMax _ i h; have := fm02; omega

theorem free_numPairLeaf {i : ℕ}
    (h : Free i (Form.fAnd (fNumF 1 0) (fNumF 0 1))) : i < 7 := by
  rcases h with h | h
  · have := free_fNumF h; omega
  · have := free_fNumF h; omega

theorem free_impClauseLeaf {i : ℕ} (h : Free i (fLevelImpF 4 3 2 6 1 0)) :
    i < 7 := by
  have := free_lt_freeMax _ i h; have := fm08; omega

theorem free_andClauseLeaf {i : ℕ} (h : Free i (fLevelAndF 4 3 2 6 1 0)) :
    i < 7 := by
  have := free_lt_freeMax _ i h; have := fm09; omega

theorem free_orClauseLeaf {i : ℕ} (h : Free i (fLevelOrF 4 3 2 6 1 0)) :
    i < 7 := by
  have := free_lt_freeMax _ i h; have := fm10; omega

theorem free_tagAllLeaf {i : ℕ} (h : Free i (fTagUnF 5 6 0)) : i < 8 := by
  have := free_lt_freeMax _ i h; have := fm11; omega

theorem free_tagExLeaf {i : ℕ} (h : Free i (fTagUnF 5 7 0)) : i < 8 := by
  have := free_lt_freeMax _ i h; have := fm12; omega

theorem free_piBoundedLeaf {i : ℕ} (h : Free i (fPiBoundedF 6 5)) : i < 8 := by
  have := free_lt_freeMax _ i h; have := fm13; omega

theorem free_sigmaBoundedLeaf {i : ℕ} (h : Free i (fSigmaBoundedF 6 5)) :
    i < 8 := by
  have := free_lt_freeMax _ i h; have := fm14; omega

theorem free_allWitnessLeaf {i : ℕ}
    (h : Free i (Form.fAnd (.fEq 3 2) (.fEx (fShiftTripleMemF 1 0 5 8 0)))) :
    i < 8 := by
  rcases h with h | h
  · rcases free_fEq h with rfl | rfl <;> omega
  · have h1 := free_lt_freeMax _ _ h
    simp only [freeMax] at h1
    have := fm15; omega

theorem free_exWitnessLeaf {i : ℕ}
    (h : Free i (Form.fAnd (.fEq 3 1) (.fEx (fShiftTripleMemF 1 0 5 8 1)))) :
    i < 8 := by
  rcases h with h | h
  · rcases free_fEq h with rfl | rfl <;> omega
  · have h1 := free_lt_freeMax _ _ h
    simp only [freeMax] at h1
    have := fm16; omega

theorem free_tripleMemInstA {i : ℕ} (h : Free i (fTripleMemF 6 5 4 1)) :
    i < 9 := by
  have := free_lt_freeMax _ i h; have := fm05; omega

theorem free_tripleMemInstB {i : ℕ} (h : Free i (fTripleMemF 7 6 4 1)) :
    i < 10 := by
  have := free_lt_freeMax _ i h; have := fm06; omega

theorem free_tripleMemInstC {i : ℕ} (h : Free i (fTripleMemF 7 6 3 1)) :
    i < 10 := by
  have := free_lt_freeMax _ i h; have := fm07; omega

theorem free_closZero {i : ℕ} (h : Free i (closF 0)) : i < 2 :=
  free_closF 0 h

theorem free_numChainZero {i : ℕ} (h : Free i (fNumF 0 0)) : i < 1 := by
  have := free_fNumF h; omega

theorem free_numChainStep {i : ℕ} (h : Free i (SetTheory.fSuccF 1 0)) :
    i < 2 := by
  rcases free_fSuccF h with rfl | rfl <;> omega

set_option maxHeartbeats 1000000 in
/-- The canonical instance's membership atom.  Kernel-evaluated here
because `ZFCinPA.LevelCodeTower` has no occasion for it. -/
theorem freeMax_tripleMemCanon : freeMax (fTripleMemF 4 3 2 1) ≤ 5 := by decide

theorem free_tripleMemCanon {i : ℕ} (h : Free i (fTripleMemF 4 3 2 1)) :
    i < 5 := by
  have := free_lt_freeMax _ i h; have := freeMax_tripleMemCanon; omega

end FreeBounds

/-! ## The two model-coded leaves are shift-fixed -/

section Leaves

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shiftFixed_tripleMemHead :
    ShiftFixed ((tripleMemHeadCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tripleMemHead h)

theorem shiftFixed_univEnvLeaf : ShiftFixed ((univEnvLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_univEnvLeaf h)

theorem shiftFixed_numPairLeaf : ShiftFixed ((numPairLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_numPairLeaf h)

theorem shiftFixed_impClauseLeaf : ShiftFixed ((impClauseLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_impClauseLeaf h)

theorem shiftFixed_andClauseLeaf : ShiftFixed ((andClauseLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_andClauseLeaf h)

theorem shiftFixed_orClauseLeaf : ShiftFixed ((orClauseLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_orClauseLeaf h)

theorem shiftFixed_tagAllLeaf : ShiftFixed ((tagAllLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tagAllLeaf h)

theorem shiftFixed_tagExLeaf : ShiftFixed ((tagExLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tagExLeaf h)

theorem shiftFixed_eqBitOneLeaf : ShiftFixed ((eqBitOneLeafCode : ℕ) : V) :=
  shiftFixed_leafCode
    (fun _ h ↦ by rcases free_fEq h with rfl | rfl <;> omega)

theorem shiftFixed_eqBitZeroLeaf : ShiftFixed ((eqBitZeroLeafCode : ℕ) : V) :=
  shiftFixed_leafCode
    (fun _ h ↦ by rcases free_fEq h with rfl | rfl <;> omega)

theorem shiftFixed_piBoundedLeaf : ShiftFixed ((piBoundedLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_piBoundedLeaf h)

theorem shiftFixed_sigmaBoundedLeaf :
    ShiftFixed ((sigmaBoundedLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_sigmaBoundedLeaf h)

theorem shiftFixed_allWitnessLeaf :
    ShiftFixed ((allWitnessLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_allWitnessLeaf h)

theorem shiftFixed_exWitnessLeaf : ShiftFixed ((exWitnessLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_exWitnessLeaf h)

theorem shiftFixed_botLeaf : ShiftFixed ((botLeafCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ absurd h (by simp [SetTheory.Free]))

theorem shiftFixed_tripleMemInstA :
    ShiftFixed ((tripleMemInstACode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tripleMemInstA h)

theorem shiftFixed_tripleMemInstB :
    ShiftFixed ((tripleMemInstBCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tripleMemInstB h)

theorem shiftFixed_tripleMemInstC :
    ShiftFixed ((tripleMemInstCCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_tripleMemInstC h)

theorem shiftFixed_closZero : ShiftFixed ((closZeroCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_closZero h)

theorem shiftFixed_numChainZero : ShiftFixed ((numChainZeroCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_numChainZero h)

theorem shiftFixed_numChainStep : ShiftFixed ((numChainStepCode : ℕ) : V) :=
  shiftFixed_leafCode (fun _ h ↦ free_numChainStep h)

/- The parameter firewall, enforced at the unification level: with the leaf
lemmas in place, nothing below may delta-unfold a named code constant — a
failed unification attempt against one would otherwise try to *evaluate*
an astronomically large Gödel code. -/
attribute [local irreducible] tripleMemHeadCode univEnvLeafCode
  numPairLeafCode impClauseLeafCode andClauseLeafCode orClauseLeafCode
  tagAllLeafCode tagExLeafCode eqBitOneLeafCode eqBitZeroLeafCode
  piBoundedLeafCode sigmaBoundedLeafCode allWitnessLeafCode
  exWitnessLeafCode botLeafCode tripleMemInstACode tripleMemInstBCode
  tripleMemInstCCode tripleMemCanonCode levelSatZeroCode closZeroCode
  numOneWitnessCode numZeroWitnessCode botCanonCode numChainZeroCode
  numChainStepCode

/-- The unfolded-instance shape preserves shift-fixedness. -/
theorem shiftFixed_lvlInstPart {num cls : V} (t : ℕ)
    (ht : ShiftFixed ((t : ℕ) : V)) (hn : ShiftFixed num)
    (hc : ShiftFixed cls) : ShiftFixed (lvlInstPart t num cls) :=
  .exs (.exs (hn.and (hc.and ht)))

/-- The coded universal clause preserves shift-fixedness. -/
theorem shiftFixed_allClauseCode {num cls : V}
    (hn : ShiftFixed num) (hc : ShiftFixed cls) :
    ShiftFixed (allClauseCode num cls) :=
  .exs (shiftFixed_tagAllLeaf.and
    ((shiftFixed_eqBitOneLeaf.and
      (shiftFixed_piBoundedLeaf.and
        ((shiftFixed_lvlInstPart _ shiftFixed_tripleMemInstB hn hc).imp
          shiftFixed_botLeaf))).or
      shiftFixed_allWitnessLeaf))

/-- The coded existential clause preserves shift-fixedness. -/
theorem shiftFixed_exClauseCode {num cls : V}
    (hn : ShiftFixed num) (hc : ShiftFixed cls) :
    ShiftFixed (exClauseCode num cls) :=
  .exs (shiftFixed_tagExLeaf.and
    (shiftFixed_exWitnessLeaf.or
      (shiftFixed_eqBitZeroLeaf.and
        (shiftFixed_sigmaBoundedLeaf.and
          ((shiftFixed_lvlInstPart _ shiftFixed_tripleMemInstC hn hc).imp
            shiftFixed_botLeaf)))))

/-- The coded justification row preserves shift-fixedness. -/
theorem shiftFixed_justRowCode {num cls : V}
    (hn : ShiftFixed num) (hc : ShiftFixed cls) :
    ShiftFixed (justRowCode num cls) :=
  .exs (.exs (shiftFixed_numPairLeaf.and
    ((shiftFixed_lvlInstPart _ shiftFixed_tripleMemInstA hn hc).or
      (shiftFixed_impClauseLeaf.or
        (shiftFixed_andClauseLeaf.or
          (shiftFixed_orClauseLeaf.or
            ((shiftFixed_allClauseCode hn hc).or
              (shiftFixed_exClauseCode hn hc))))))))

/-- **The closure step preserves shift-fixedness.**  Pure spine
decomposition: the nineteen fixed leaves are the named lemmas above, the
two tower slots are the hypotheses, and every node is one introduction
rule.  The term is written out rather than searched for, so no unification
step ever has to look inside a named Gödel constant. -/
theorem shiftFixed_closStepCode {num cls : V}
    (hn : ShiftFixed num) (hc : ShiftFixed cls) :
    ShiftFixed (closStepCode num cls) :=
  .all (.all (.all (shiftFixed_tripleMemHead.imp
    (shiftFixed_univEnvLeaf.and (shiftFixed_justRowCode hn hc)))))

/-- **The numeral chain is shift-fixed at every model index.** -/
theorem shift_numChainCode (x : V) :
    Bootstrapping.shift ℒₛₑₜ (numChainCode x) = numChainCode x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [numChainCode_zero]
    exact (shiftFixed_numChainZero (V := V)).2
  case succ x ih =>
    rw [numChainCode_succ]
    exact (ShiftFixed.exs
      (ShiftFixed.and ⟨(isSemiformula_numChainCode x).isUFormula, ih⟩
        shiftFixed_numChainStep)).2

theorem shiftFixed_numChainCode (x : V) : ShiftFixed (numChainCode x) :=
  ⟨(isSemiformula_numChainCode x).isUFormula, shift_numChainCode x⟩

/-- **The closure kernel is shift-fixed at every model index.** -/
theorem shift_closCode (x : V) :
    Bootstrapping.shift ℒₛₑₜ (closCode x) = closCode x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [closCode_zero]
    exact (shiftFixed_closZero (V := V)).2
  case succ x ih =>
    rw [closCode_succ]
    exact (shiftFixed_closStepCode (shiftFixed_numChainCode x)
      ⟨(isSemiformula_closCode x).isUFormula, ih⟩).2

theorem shiftFixed_closCode (x : V) : ShiftFixed (closCode x) :=
  ⟨(isSemiformula_closCode x).isUFormula, shift_closCode x⟩

end Leaves

/-! ## The template language of the level tower -/

/-- The two `x`-dependent leaves of every certificate field: the numeral
chain (unary) and the closure kernel (binary). -/
@[reducible] def levelArities : Fin 2 → ℕ := ![1, 2]

/-- The placeholder-enlarged source language of the level tower. -/
@[reducible] def srcL : Language := setTemplateLanguage 2 levelArities

section Source

open SetTheory (Form Free)

/-- Proposition-level placeholder atom.  `SetPlaceholders.srcP` is
sentence-valued; the fixed `ℒₛₑₜ` leaves of the field spines are
`toSet`-translations, which are `Semiproposition`s, so the whole source
formula is assembled at the proposition level and closed at the very
end. -/
def srcPProp {n : ℕ} (i : Fin 2)
    (ts : Fin (levelArities i) → SyntacticSemiterm srcL n) :
    Semiproposition srcL n :=
  .rel (placeholderRel i) ts

/-- The `i`-th placeholder applied to the identity argument list
`#0, …, #(levelArities i - 1)`, at an ambient arity that can accommodate
it. -/
def srcPlaceholder {n : ℕ} (i : Fin 2) (h : levelArities i ≤ n) :
    Semiproposition srcL n :=
  srcPProp i fun j ↦ #(Fin.castLE h j)

/-- A fixed `ℒₛₑₜ` leaf, lifted into the source language. -/
noncomputable def liftP {n : ℕ} (φ : SetTheorySemiproposition n) :
    Semiproposition srcL n :=
  φ.lMap (setHom 2 levelArities)

/-- The numeral-chain placeholder at any ambient arity that can hold it. -/
noncomputable def srcNumAt {n : ℕ} (h : 1 ≤ n) : Semiproposition srcL n :=
  srcPlaceholder 0 (by simpa [levelArities] using h)

/-- The closure-kernel placeholder at any ambient arity that can hold it. -/
noncomputable def srcClsAt {n : ℕ} (h : 2 ≤ n) : Semiproposition srcL n :=
  srcPlaceholder 1 (by simpa [levelArities] using h)

end Source

/-! ## Reconciliation of the two atom shapes -/

section Translate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open SetTheory (Form Free)

/-- **The placeholder atom specializes to the raw leaf.**  This is the
compiler-facing form of `ZFCinPA.SubstIdentity`: the translation always
emits a substitution, and the identity bound-variable vector makes it
vanish even though the leaf's own arity is smaller than the ambient one. -/
theorem translate_srcPlaceholder {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (i : Fin 2) (h : levelArities i ≤ n) :
    (translateFormula Ks (srcPlaceholder i h)).val = (Ks i).val := by
  show ((Ks i).subst
    (fun j ↦ translateTerm (V := V)
      ((fun j ↦ #(Fin.castLE h j)) (Fin.cast rfl j)))).val = (Ks i).val
  exact Semiformula.subst_bvarVec_val (Ks i) _ fun _ ↦ rfl

/-- A lifted fixed leaf specializes to its quotation. -/
theorem translate_liftP {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (φ : SetTheorySemiproposition n) :
    translateFormula Ks (liftP φ) = (⌜φ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ n) :=
  translateFormula_lMap_set Ks φ

/-- Raw-code form of `translate_liftP`. -/
theorem translate_liftP_val {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (φ : SetTheorySemiproposition n) :
    (translateFormula Ks (liftP φ)).val = (⌜φ⌝ : V) := by
  rw [translate_liftP]; rfl

/-- Specialization commutes with conjunction. -/
theorem translate_and {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p q : Semiproposition srcL n) :
    translateFormula Ks (p ⋏ q) =
      translateFormula Ks p ⋏ translateFormula Ks q := rfl

/-- Specialization commutes with disjunction. -/
theorem translate_or {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p q : Semiproposition srcL n) :
    translateFormula Ks (p ⋎ q) =
      translateFormula Ks p ⋎ translateFormula Ks q := rfl

/-- Specialization commutes with the universal quantifier. -/
theorem translate_all {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p : Semiproposition srcL (n + 1)) :
    translateFormula Ks (∀⁰ p) = ∀⁰ translateFormula Ks p := rfl

/-- Specialization commutes with the existential quantifier. -/
theorem translate_exs {n : ℕ}
    (Ks : (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i))
    (p : Semiproposition srcL (n + 1)) :
    translateFormula Ks (∃⁰ p) = ∃⁰ translateFormula Ks p := rfl

/-- **The depth move, packaged.**  A fixed leaf's quote at the ambient
depth `k` is the named constant computed at the declared depth `d`,
provided every free slot of the underlying `Form` lies below both.  This is
the only way a concrete Gödel code is ever touched below — never by
`simp`, never by evaluation. -/
theorem quote_toSet_eq_code {φ : Form} {k d : ℕ}
    (hk : ∀ i, Free i φ → i < k) (hd : ∀ i, Free i φ → i < d) :
    (⌜toSet k φ⌝ : V) = (((toSet d φ).toNat : ℕ) : V) := by
  rw [quote_toSet_congr hk hd, coe_toNat_eq_quote]

/-- `quote_toSet_eq_code` with the moved formula and both depths explicit.
The spine proofs below name every leaf, so no `rw` ever has to guess which
occurrence it is rewriting. -/
theorem quote_leaf_move (φ : Form) (k d : ℕ)
    (hk : ∀ i, Free i φ → i < k) (hd : ∀ i, Free i φ → i < d) :
    (⌜toSet k φ⌝ : V) = (((toSet d φ).toNat : ℕ) : V) :=
  quote_toSet_eq_code hk hd

end Translate

/-! ## The two model-coded leaves, typed -/

section TypedLeaves

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two `x`-dependent leaves of the level tower, typed at their own
arities: the numeral chain and the closure kernel. -/
noncomputable def levelLeaves (x : V) :
    (i : Fin 2) → Bootstrapping.Semiformula V ℒₛₑₜ (levelArities i)
  | ⟨0, _⟩ => ⟨numChainCode x, by simpa using isSemiformula_numChainCode x⟩
  | ⟨1, _⟩ => ⟨closCode x, by simpa using isSemiformula_closCode x⟩

@[simp] theorem levelLeaves_zero (x : V) :
    (levelLeaves x 0).val = numChainCode x := rfl

@[simp] theorem levelLeaves_one (x : V) :
    (levelLeaves x 1).val = closCode x := rfl

/-- **The two model-coded leaves are shift-fixed**, which is exactly the
hypothesis `SetPlaceholders.compileSetTemplate` places on an
interpretation of the placeholders. -/
theorem shift_levelLeaves (x : V) : ∀ i : Fin 2,
    Bootstrapping.shift ℒₛₑₜ (levelLeaves x i).val = (levelLeaves x i).val
  | ⟨0, _⟩ => shift_numChainCode x
  | ⟨1, _⟩ => shift_closCode x

theorem translate_srcNumAt {n : ℕ} (h : 1 ≤ n) (x : V) :
    (translateFormula (levelLeaves x) (srcNumAt h)).val = numChainCode x :=
  translate_srcPlaceholder (levelLeaves x) 0 _

theorem translate_srcClsAt {n : ℕ} (h : 2 ≤ n) (x : V) :
    (translateFormula (levelLeaves x) (srcClsAt h)).val = closCode x :=
  translate_srcPlaceholder (levelLeaves x) 1 _

end TypedLeaves

/-! ## The unfolded-instance shape at the source level -/

section LvlInst

open SetTheory (Form Free)

/-- Source counterpart of `LevelCodeTower.lvlInstPart`: two existentials
over a numeral formula, a closure formula, and one fixed membership
atom. -/
noncomputable def srcLvlInst (m : ℕ) (atom : Form)
    (num cls : Semiproposition srcL (m + 1 + 1)) : Semiproposition srcL m :=
  ∃⁰ ∃⁰ (num ⋏ (cls ⋏ liftP (toSet (m + 1 + 1) atom)))

/-- The unfolded instance whose two slots are the *placeholders*, i.e. the
level-`x` numeral chain and closure kernel. -/
noncomputable def srcLvlInstP (m : ℕ) (atom : Form) : Semiproposition srcL m :=
  srcLvlInst m atom (srcNumAt (by omega)) (srcClsAt (by omega))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcLvlInst (x : V) (m : ℕ) (atom : Form) (d : ℕ)
    (hm : ∀ i, Free i atom → i < m + 1 + 1)
    (hd : ∀ i, Free i atom → i < d)
    (num cls : Semiproposition srcL (m + 1 + 1)) :
    (translateFormula (levelLeaves x) (srcLvlInst m atom num cls)).val =
      lvlInstPart ((toSet d atom).toNat)
        (translateFormula (levelLeaves x) num).val
        (translateFormula (levelLeaves x) cls).val := by
  simp only [srcLvlInst, lvlInstPart, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val]
  rw [quote_leaf_move (V := V) atom (m + 1 + 1) d hm hd]

theorem translate_srcLvlInstP (x : V) (m : ℕ) (atom : Form) (d : ℕ)
    (hm : ∀ i, Free i atom → i < m + 1 + 1)
    (hd : ∀ i, Free i atom → i < d) :
    (translateFormula (levelLeaves x) (srcLvlInstP m atom)).val =
      lvlInstPart ((toSet d atom).toNat) (numChainCode x) (closCode x) := by
  unfold srcLvlInstP
  rw [translate_srcLvlInst x m atom d hm hd, translate_srcNumAt,
    translate_srcClsAt]

end LvlInst

/-! ## The source level tower at the canonical slots -/

section SourceTower

open SetTheory (Form Free)

/-- The unfolded canonical level instance at the *successor* index: two
existentials over the numeral chain and the closure kernel, and the fixed
membership atom.  Both placeholders carry the identity argument list, so
their specializations are the raw leaves. -/
noncomputable def srcLevelSat : Semiproposition srcL 5 :=
  srcLvlInstP 5 (fTripleMemF 4 3 2 1)

/-- Sigma-truth at the successor index, canonical slots. -/
noncomputable def srcSigmaTrue : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 1)) ⋏ srcLevelSat)

/-- Pi-falsity at the successor index, canonical slots. -/
noncomputable def srcPiFalse : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 0)) ⋏ srcLevelSat)

/-- Pi-truth at the successor index: the negation of Pi-falsity. -/
noncomputable def srcPiTrue : Semiproposition srcL 4 :=
  srcPiFalse 🡒 liftP (toSet 4 Form.fBot)

/-- The canonical-slot gadget at the pair `(1, 0)`: two universal
quantifiers over the two equality guards and the payload. -/
noncomputable def srcCanonAt (inner : Semiproposition srcL 4) :
    Semiproposition srcL 2 :=
  ∀⁰ ∀⁰ (liftP (toSet 4 (Form.fEq 1 3)) 🡒
    (liftP (toSet 4 (Form.fEq 0 2)) 🡒 inner))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The canonical level instance. -/
theorem translate_srcLevelSat (x : V) :
    (translateFormula (levelLeaves x) srcLevelSat).val = levelSatCode (x + 1) := by
  rw [levelSatCode_succ]
  exact translate_srcLvlInstP x 5 (fTripleMemF 4 3 2 1) 5
    (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
    (fun i hi ↦ free_tripleMemCanon hi)

/-- Sigma-truth at the successor index. -/
theorem translate_srcSigmaTrue (x : V) :
    (translateFormula (levelLeaves x) srcSigmaTrue).val =
      sigmaTrueCode (x + 1) := by
  rw [sigmaTrueCode, bitWitnessPart]
  simp only [srcSigmaTrue, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSat]
  rw [quote_leaf_move (V := V) (fNumF 0 1) 5 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

/-- Pi-falsity at the successor index. -/
theorem translate_srcPiFalse (x : V) :
    (translateFormula (levelLeaves x) srcPiFalse).val =
      piFalseCode (x + 1) := by
  rw [piFalseCode, bitWitnessPart]
  simp only [srcPiFalse, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSat]
  rw [quote_leaf_move (V := V) (fNumF 0 0) 5 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

/-- Pi-truth at the successor index. -/
theorem translate_srcPiTrue (x : V) :
    (translateFormula (levelLeaves x) srcPiTrue).val =
      piTrueCode (x + 1) := by
  rw [piTrueCode, piTruePart]
  simp only [srcPiTrue, translateFormula_imp,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcPiFalse]
  rw [quote_leaf_move (V := V) Form.fBot 4 2
    (fun i hi ↦ absurd hi (by simp [Free]))
    (fun i hi ↦ absurd hi (by simp [Free]))]
  rfl

/-- The canonical-slot gadget. -/
theorem translate_srcCanonAt (x : V) (inner : Semiproposition srcL 4) :
    (translateFormula (levelLeaves x) (srcCanonAt inner)).val =
      canonAtPart (eqGuardCode 1 3) (eqGuardCode 0 2)
        (translateFormula (levelLeaves x) inner).val := by
  rw [canonAtPart]
  simp only [srcCanonAt, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val]
  rw [quote_fEq_move (V := V) (show 1 < 4 by omega) (show 3 < 4 by omega),
    quote_fEq_move (V := V) (show 0 < 4 by omega) (show 2 < 4 by omega)]

end SourceTower

/-! ## The successor step of the two towers, at the source level

This is the piece the *successor* side of every certificate field needs:
`numChainCode (x + 1)` and `closCode (x + 1)` written out over the
level-`x` placeholders.  `closCode (x + 1) = closStepCode (numChainCode x)
(closCode x)` is the nineteen-leaf `closStepPart`/`justRowPart`/
`allClausePart`/`exClausePart`/`lvlInstPart` spine of
`ZFCinPA.LevelCodeTower`, so the source counterpart is written in the same
four layers, each at an arbitrary ambient arity with one depth move per
fixed leaf.  The ambient-arity hypotheses are exactly the conditions under
which every fixed leaf's declared depth is available. -/

section SuccessorSpine

open SetTheory (Form Free)

/-- Source counterpart of `numChainCode (x + 1)`. -/
noncomputable def srcNumChainSucc (m : ℕ) : Semiproposition srcL m :=
  ∃⁰ (srcNumAt (n := m + 1) (by omega) ⋏
    liftP (toSet (m + 1) (SetTheory.fSuccF 1 0)))

/-- Source counterpart of `allClauseCode`, the justification row's
universal clause. -/
noncomputable def srcAllClause (m : ℕ) : Semiproposition srcL m :=
  ∃⁰ (liftP (toSet (m + 1) (fTagUnF 5 6 0)) ⋏
    ((liftP (toSet (m + 1) (Form.fEq 3 1)) ⋏
      (liftP (toSet (m + 1) (fPiBoundedF 6 5)) ⋏
        (srcLvlInstP (m + 1) (fTripleMemF 7 6 4 1) 🡒
          liftP (toSet (m + 1) Form.fBot)))) ⋎
     liftP (toSet (m + 1)
       (Form.fAnd (.fEq 3 2) (.fEx (fShiftTripleMemF 1 0 5 8 0))))))

/-- Source counterpart of `exClauseCode`, the justification row's
existential clause. -/
noncomputable def srcExClause (m : ℕ) : Semiproposition srcL m :=
  ∃⁰ (liftP (toSet (m + 1) (fTagUnF 5 7 0)) ⋏
    (liftP (toSet (m + 1)
       (Form.fAnd (.fEq 3 1) (.fEx (fShiftTripleMemF 1 0 5 8 1)))) ⋎
     (liftP (toSet (m + 1) (Form.fEq 3 2)) ⋏
      (liftP (toSet (m + 1) (fSigmaBoundedF 6 5)) ⋏
        (srcLvlInstP (m + 1) (fTripleMemF 7 6 3 1) 🡒
          liftP (toSet (m + 1) Form.fBot))))))

/-- Source counterpart of `justRowCode`. -/
noncomputable def srcJustRow (m : ℕ) : Semiproposition srcL m :=
  ∃⁰ ∃⁰ (liftP (toSet (m + 1 + 1) (Form.fAnd (fNumF 1 0) (fNumF 0 1))) ⋏
    (srcLvlInstP (m + 1 + 1) (fTripleMemF 6 5 4 1) ⋎
     (liftP (toSet (m + 1 + 1) (fLevelImpF 4 3 2 6 1 0)) ⋎
      (liftP (toSet (m + 1 + 1) (fLevelAndF 4 3 2 6 1 0)) ⋎
       (liftP (toSet (m + 1 + 1) (fLevelOrF 4 3 2 6 1 0)) ⋎
        (srcAllClause (m + 1 + 1) ⋎ srcExClause (m + 1 + 1)))))))

/-- **Source counterpart of `closCode (x + 1)`.**  Three universal
quantifiers over the head membership atom, the environment condition and
the justification row. -/
noncomputable def srcClosStep (m : ℕ) : Semiproposition srcL m :=
  ∀⁰ ∀⁰ ∀⁰ (liftP (toSet (m + 1 + 1 + 1) (fTripleMemF 2 1 0 4)) 🡒
    (liftP (toSet (m + 1 + 1 + 1) (fUnivEnvF 1)) ⋏
      srcJustRow (m + 1 + 1 + 1)))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcNumChainSucc (x : V) (m : ℕ) (hm : 1 ≤ m) :
    (translateFormula (levelLeaves x) (srcNumChainSucc m)).val =
      numChainCode (x + 1) := by
  rw [numChainCode_succ]
  simp only [srcNumChainSucc, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcNumAt]
  rw [quote_leaf_move (V := V) (SetTheory.fSuccF 1 0) (m + 1) 2
    (fun i hi ↦ by rcases free_fSuccF hi with rfl | rfl <;> omega)
    (fun i hi ↦ by rcases free_fSuccF hi with rfl | rfl <;> omega)]
  rfl

theorem translate_srcAllClause (x : V) (m : ℕ) (hm : 7 ≤ m) :
    (translateFormula (levelLeaves x) (srcAllClause m)).val =
      allClauseCode (numChainCode x) (closCode x) := by
  rw [allClauseCode, allClausePart]
  simp only [srcAllClause, translate_exs, translate_and, translate_or,
    translateFormula_imp, Bootstrapping.Semiformula.val_exs,
    Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_or,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val]
  rw [translate_srcLvlInstP x (m + 1) (fTripleMemF 7 6 4 1) 10
      (fun i hi ↦ by have := free_tripleMemInstB hi; omega)
      (fun i hi ↦ by have := free_tripleMemInstB hi; omega),
    quote_leaf_move (V := V) (fTagUnF 5 6 0) (m + 1) 8
      (fun i hi ↦ by have := free_tagAllLeaf hi; omega)
      (fun i hi ↦ free_tagAllLeaf hi),
    quote_leaf_move (V := V) (Form.fEq 3 1) (m + 1) 8
      (fun i hi ↦ by rcases free_fEq hi with rfl | rfl <;> omega)
      (fun i hi ↦ by rcases free_fEq hi with rfl | rfl <;> omega),
    quote_leaf_move (V := V) (fPiBoundedF 6 5) (m + 1) 8
      (fun i hi ↦ by have := free_piBoundedLeaf hi; omega)
      (fun i hi ↦ free_piBoundedLeaf hi),
    quote_leaf_move (V := V) Form.fBot (m + 1) 8
      (fun i hi ↦ absurd hi (by simp [Free]))
      (fun i hi ↦ absurd hi (by simp [Free])),
    quote_leaf_move (V := V)
      (Form.fAnd (.fEq 3 2) (.fEx (fShiftTripleMemF 1 0 5 8 0))) (m + 1) 8
      (fun i hi ↦ by have := free_allWitnessLeaf hi; omega)
      (fun i hi ↦ free_allWitnessLeaf hi)]
  rfl

theorem translate_srcExClause (x : V) (m : ℕ) (hm : 7 ≤ m) :
    (translateFormula (levelLeaves x) (srcExClause m)).val =
      exClauseCode (numChainCode x) (closCode x) := by
  rw [exClauseCode, exClausePart]
  simp only [srcExClause, translate_exs, translate_and, translate_or,
    translateFormula_imp, Bootstrapping.Semiformula.val_exs,
    Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_or,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val]
  rw [translate_srcLvlInstP x (m + 1) (fTripleMemF 7 6 3 1) 10
      (fun i hi ↦ by have := free_tripleMemInstC hi; omega)
      (fun i hi ↦ by have := free_tripleMemInstC hi; omega),
    quote_leaf_move (V := V) (fTagUnF 5 7 0) (m + 1) 8
      (fun i hi ↦ by have := free_tagExLeaf hi; omega)
      (fun i hi ↦ free_tagExLeaf hi),
    quote_leaf_move (V := V)
      (Form.fAnd (.fEq 3 1) (.fEx (fShiftTripleMemF 1 0 5 8 1))) (m + 1) 8
      (fun i hi ↦ by have := free_exWitnessLeaf hi; omega)
      (fun i hi ↦ free_exWitnessLeaf hi),
    quote_leaf_move (V := V) (Form.fEq 3 2) (m + 1) 8
      (fun i hi ↦ by rcases free_fEq hi with rfl | rfl <;> omega)
      (fun i hi ↦ by rcases free_fEq hi with rfl | rfl <;> omega),
    quote_leaf_move (V := V) (fSigmaBoundedF 6 5) (m + 1) 8
      (fun i hi ↦ by have := free_sigmaBoundedLeaf hi; omega)
      (fun i hi ↦ free_sigmaBoundedLeaf hi),
    quote_leaf_move (V := V) Form.fBot (m + 1) 8
      (fun i hi ↦ absurd hi (by simp [Free]))
      (fun i hi ↦ absurd hi (by simp [Free]))]
  rfl

theorem translate_srcJustRow (x : V) (m : ℕ) (hm : 5 ≤ m) :
    (translateFormula (levelLeaves x) (srcJustRow m)).val =
      justRowCode (numChainCode x) (closCode x) := by
  rw [justRowCode, justRowPart]
  simp only [srcJustRow, translate_exs, translate_and, translate_or,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_or, translate_liftP_val,
    translate_srcAllClause x (m + 1 + 1) (by omega),
    translate_srcExClause x (m + 1 + 1) (by omega)]
  rw [translate_srcLvlInstP x (m + 1 + 1) (fTripleMemF 6 5 4 1) 9
      (fun i hi ↦ by have := free_tripleMemInstA hi; omega)
      (fun i hi ↦ free_tripleMemInstA hi),
    quote_leaf_move (V := V) (Form.fAnd (fNumF 1 0) (fNumF 0 1)) (m + 1 + 1) 7
      (fun i hi ↦ by have := free_numPairLeaf hi; omega)
      (fun i hi ↦ free_numPairLeaf hi),
    quote_leaf_move (V := V) (fLevelImpF 4 3 2 6 1 0) (m + 1 + 1) 7
      (fun i hi ↦ by have := free_impClauseLeaf hi; omega)
      (fun i hi ↦ free_impClauseLeaf hi),
    quote_leaf_move (V := V) (fLevelAndF 4 3 2 6 1 0) (m + 1 + 1) 7
      (fun i hi ↦ by have := free_andClauseLeaf hi; omega)
      (fun i hi ↦ free_andClauseLeaf hi),
    quote_leaf_move (V := V) (fLevelOrF 4 3 2 6 1 0) (m + 1 + 1) 7
      (fun i hi ↦ by have := free_orClauseLeaf hi; omega)
      (fun i hi ↦ free_orClauseLeaf hi)]
  rfl

/-- **The source counterpart of `closCode_succ`.**  At every model index
and every ambient arity that can hold a binary formula, the source spine
specializes to the next level's closure kernel. -/
theorem translate_srcClosStep (x : V) (m : ℕ) (hm : 2 ≤ m) :
    (translateFormula (levelLeaves x) (srcClosStep m)).val =
      closCode (x + 1) := by
  rw [closCode_succ, closStepCode, closStepPart]
  simp only [srcClosStep, translate_all, translate_and, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcJustRow x (m + 1 + 1 + 1) (by omega)]
  rw [quote_leaf_move (V := V) (fTripleMemF 2 1 0 4) (m + 1 + 1 + 1) 5
      (fun i hi ↦ by have := free_tripleMemHead hi; omega)
      (fun i hi ↦ free_tripleMemHead hi),
    quote_leaf_move (V := V) (fUnivEnvF 1) (m + 1 + 1 + 1) 5
      (fun i hi ↦ by have := free_univEnvLeaf hi; omega)
      (fun i hi ↦ free_univEnvLeaf hi)]
  rfl

end SuccessorSpine

/-! ## The source level tower one level up

The successor side of all five fields reads the level-`(x+2)` truth
formulas, which are the canonical wrappers around the level-`(x+2)`
instance — and *that* instance is built from the two successor spines
above, not from the placeholders directly. -/

section SourceTowerSucc

open SetTheory (Form Free)

/-- The canonical level instance two levels up. -/
noncomputable def srcLevelSatSucc : Semiproposition srcL 5 :=
  srcLvlInst 5 (fTripleMemF 4 3 2 1) (srcNumChainSucc 7) (srcClosStep 7)

/-- Sigma-truth two levels up, canonical slots. -/
noncomputable def srcSigmaTrueSucc : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 1)) ⋏ srcLevelSatSucc)

/-- Pi-falsity two levels up, canonical slots. -/
noncomputable def srcPiFalseSucc : Semiproposition srcL 4 :=
  ∃⁰ (liftP (toSet 5 (fNumF 0 0)) ⋏ srcLevelSatSucc)

/-- Pi-truth two levels up. -/
noncomputable def srcPiTrueSucc : Semiproposition srcL 4 :=
  srcPiFalseSucc 🡒 liftP (toSet 4 Form.fBot)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcLevelSatSucc (x : V) :
    (translateFormula (levelLeaves x) srcLevelSatSucc).val =
      levelSatCode (x + 1 + 1) := by
  rw [levelSatCode_succ]
  unfold srcLevelSatSucc
  rw [translate_srcLvlInst x 5 (fTripleMemF 4 3 2 1) 5
      (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
      (fun i hi ↦ free_tripleMemCanon hi),
    translate_srcNumChainSucc x 7 (by omega),
    translate_srcClosStep x 7 (by omega)]
  rfl

theorem translate_srcSigmaTrueSucc (x : V) :
    (translateFormula (levelLeaves x) srcSigmaTrueSucc).val =
      sigmaTrueCode (x + 1 + 1) := by
  rw [sigmaTrueCode, bitWitnessPart]
  simp only [srcSigmaTrueSucc, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSatSucc]
  rw [quote_leaf_move (V := V) (fNumF 0 1) 5 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

theorem translate_srcPiFalseSucc (x : V) :
    (translateFormula (levelLeaves x) srcPiFalseSucc).val =
      piFalseCode (x + 1 + 1) := by
  rw [piFalseCode, bitWitnessPart]
  simp only [srcPiFalseSucc, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSatSucc]
  rw [quote_leaf_move (V := V) (fNumF 0 0) 5 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

theorem translate_srcPiTrueSucc (x : V) :
    (translateFormula (levelLeaves x) srcPiTrueSucc).val =
      piTrueCode (x + 1 + 1) := by
  rw [piTrueCode, piTruePart]
  simp only [srcPiTrueSucc, translateFormula_imp,
    Bootstrapping.Semiformula.val_imp, translate_liftP_val,
    translate_srcPiFalseSucc]
  rw [quote_leaf_move (V := V) Form.fBot 4 2
    (fun i hi ↦ absurd hi (by simp [Free]))
    (fun i hi ↦ absurd hi (by simp [Free]))]
  rfl

end SourceTowerSucc

/-! ## Free-variable-freeness of the source layer

`SetPlaceholders.compileSetTemplate` consumes a `Sentence srcL`, whereas
the field spines are assembled at the *proposition* level, because the
fixed leaves `toSet k φ` are `Semiproposition`s.  The two are reconciled
by `Semiformula.univCl`, which is the identity on free-variable-free
propositions — so each field needs to know that its source formula has no
free variables.  That is again a pure spine walk, and again the shared
part of it belongs here. -/

section FvFree

open SetTheory (Form Free)

/-- A source formula with no free variables. -/
def FvFree {n : ℕ} (p : Semiproposition srcL n) : Prop :=
  p.freeVariables = ∅

theorem FvFree.and {n : ℕ} {p q : Semiproposition srcL n}
    (hp : FvFree p) (hq : FvFree q) : FvFree (p ⋏ q) := by
  simp [FvFree] at hp hq ⊢; simp [hp, hq]

theorem FvFree.or {n : ℕ} {p q : Semiproposition srcL n}
    (hp : FvFree p) (hq : FvFree q) : FvFree (p ⋎ q) := by
  simp [FvFree] at hp hq ⊢; simp [hp, hq]

theorem FvFree.imp {n : ℕ} {p q : Semiproposition srcL n}
    (hp : FvFree p) (hq : FvFree q) : FvFree (p 🡒 q) := by
  simp [FvFree] at hp hq ⊢; simp [hp, hq]

theorem FvFree.all {n : ℕ} {p : Semiproposition srcL (n + 1)}
    (hp : FvFree p) : FvFree (∀⁰ p) := by
  simp [FvFree] at hp ⊢; simp [hp]

theorem FvFree.exs {n : ℕ} {p : Semiproposition srcL (n + 1)}
    (hp : FvFree p) : FvFree (∃⁰ p) := by
  simp [FvFree] at hp ⊢; simp [hp]

/-- A lifted fixed leaf whose free slots all lie below its declared depth
has no free variables. -/
theorem fvFree_liftP {n : ℕ} {φ : Form} (h : ∀ i, Free i φ → i < n) :
    FvFree (liftP (toSet n φ)) := by
  simp [FvFree, liftP, freeVariables_toSet φ n h]

/-- A placeholder atom carries only bound variables. -/
theorem fvFree_srcPlaceholder {n : ℕ} (i : Fin 2) (h : levelArities i ≤ n) :
    FvFree (srcPlaceholder i h) := by
  simp only [FvFree, srcPlaceholder, srcPProp,
    FirstOrder.Semiformula.freeVariables_rel]
  ext y
  simp

theorem fvFree_srcNumAt {n : ℕ} (h : 1 ≤ n) : FvFree (srcNumAt h) :=
  fvFree_srcPlaceholder 0 _

theorem fvFree_srcClsAt {n : ℕ} (h : 2 ≤ n) : FvFree (srcClsAt h) :=
  fvFree_srcPlaceholder 1 _

theorem fvFree_srcLvlInst {m : ℕ} {atom : Form}
    (ha : ∀ i, Free i atom → i < m + 1 + 1)
    {num cls : Semiproposition srcL (m + 1 + 1)}
    (hn : FvFree num) (hc : FvFree cls) :
    FvFree (srcLvlInst m atom num cls) :=
  .exs (.exs (hn.and (hc.and (fvFree_liftP ha))))

theorem fvFree_srcLvlInstP {m : ℕ} {atom : Form}
    (ha : ∀ i, Free i atom → i < m + 1 + 1) :
    FvFree (srcLvlInstP m atom) :=
  fvFree_srcLvlInst ha (fvFree_srcNumAt _) (fvFree_srcClsAt _)

theorem fvFree_srcLevelSat : FvFree srcLevelSat :=
  fvFree_srcLvlInstP (fun i hi ↦ by have := free_tripleMemCanon hi; omega)

theorem fvFree_srcNumChainSucc (m : ℕ) (hm : 1 ≤ m) :
    FvFree (srcNumChainSucc m) :=
  .exs ((fvFree_srcNumAt _).and
    (fvFree_liftP (fun i hi ↦ by
      rcases free_fSuccF hi with rfl | rfl <;> omega)))

theorem fvFree_srcAllClause (m : ℕ) (hm : 7 ≤ m) : FvFree (srcAllClause m) := by
  refine FvFree.exs (FvFree.and ?_ (FvFree.or
    (FvFree.and ?_ (FvFree.and ?_ (FvFree.imp ?_ ?_))) ?_))
  · exact fvFree_liftP (fun i hi ↦ by have := free_tagAllLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_piBoundedLeaf hi; omega)
  · exact fvFree_srcLvlInstP (fun i hi ↦ by
      have := free_tripleMemInstB hi; omega)
  · exact fvFree_liftP (fun i hi ↦ absurd hi (by simp [Free]))
  · exact fvFree_liftP (fun i hi ↦ by have := free_allWitnessLeaf hi; omega)

theorem fvFree_srcExClause (m : ℕ) (hm : 7 ≤ m) : FvFree (srcExClause m) := by
  refine FvFree.exs (FvFree.and ?_ (FvFree.or ?_
    (FvFree.and ?_ (FvFree.and ?_ (FvFree.imp ?_ ?_)))))
  · exact fvFree_liftP (fun i hi ↦ by have := free_tagExLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_exWitnessLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_sigmaBoundedLeaf hi; omega)
  · exact fvFree_srcLvlInstP (fun i hi ↦ by
      have := free_tripleMemInstC hi; omega)
  · exact fvFree_liftP (fun i hi ↦ absurd hi (by simp [Free]))

theorem fvFree_srcJustRow (m : ℕ) (hm : 5 ≤ m) : FvFree (srcJustRow m) := by
  refine FvFree.exs (FvFree.exs (FvFree.and ?_ (FvFree.or ?_ (FvFree.or ?_
    (FvFree.or ?_ (FvFree.or ?_ (FvFree.or ?_ ?_)))))))
  · exact fvFree_liftP (fun i hi ↦ by have := free_numPairLeaf hi; omega)
  · exact fvFree_srcLvlInstP (fun i hi ↦ by
      have := free_tripleMemInstA hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_impClauseLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_andClauseLeaf hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_orClauseLeaf hi; omega)
  · exact fvFree_srcAllClause (m + 1 + 1) (by omega)
  · exact fvFree_srcExClause (m + 1 + 1) (by omega)

theorem fvFree_srcClosStep (m : ℕ) (hm : 2 ≤ m) : FvFree (srcClosStep m) := by
  refine FvFree.all (FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.and ?_ ?_))))
  · exact fvFree_liftP (fun i hi ↦ by have := free_tripleMemHead hi; omega)
  · exact fvFree_liftP (fun i hi ↦ by have := free_univEnvLeaf hi; omega)
  · exact fvFree_srcJustRow (m + 1 + 1 + 1) (by omega)

theorem fvFree_srcLevelSatSucc : FvFree srcLevelSatSucc :=
  fvFree_srcLvlInst (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
    (fvFree_srcNumChainSucc 7 (by omega)) (fvFree_srcClosStep 7 (by omega))

theorem fvFree_srcSigmaTrue : FvFree srcSigmaTrue :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    fvFree_srcLevelSat)

theorem fvFree_srcPiFalse : FvFree srcPiFalse :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    fvFree_srcLevelSat)

theorem fvFree_srcPiTrue : FvFree srcPiTrue :=
  fvFree_srcPiFalse.imp (fvFree_liftP (fun i hi ↦ absurd hi (by simp [Free])))

theorem fvFree_srcSigmaTrueSucc : FvFree srcSigmaTrueSucc :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    fvFree_srcLevelSatSucc)

theorem fvFree_srcPiFalseSucc : FvFree srcPiFalseSucc :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    fvFree_srcLevelSatSucc)

theorem fvFree_srcPiTrueSucc : FvFree srcPiTrueSucc :=
  fvFree_srcPiFalseSucc.imp
    (fvFree_liftP (fun i hi ↦ absurd hi (by simp [Free])))

theorem fvFree_srcCanonAt {inner : Semiproposition srcL 4}
    (h : FvFree inner) : FvFree (srcCanonAt inner) := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_ h)))
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)

/-- **The closure of a free-variable-free source proposition is a source
sentence with the same embedding.**  This is what turns a field's
proposition-level source formula into the `Sentence srcL` that
`SetPlaceholders.compileSetTemplate` consumes. -/
theorem emb_univCl_of_fvFree {p : Proposition srcL} (h : FvFree p) :
    (Rewriting.emb (FirstOrder.Semiformula.univCl p) : Proposition srcL) = p := by
  have hc : ((FirstOrder.Semiformula.univCl p : Sentence srcL) :
      Proposition srcL) = p := by
    rw [FirstOrder.Semiformula.coe_univCl_eq_univCl',
      FirstOrder.Semiformula.univCl'_eq_self_of _ h]
  simpa using hc

end FvFree

end SuccessorSources
end ZFCinPA
end LeanProofs
