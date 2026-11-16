import DiophantineConsistency.IPRAPA196Consistency
import DiophantineConsistency.IPRABoundedInduction
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAImpGG
import DiophantineConsistency.IPRANativeDisjunctionWitness
import DiophantineConsistency.IPRABoundedMappedErasure
import DiophantineConsistency.IPRARefutationWitnessBridge
import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.PRAISigmaOneOriginalEquivalence
import DiophantineConsistency.PRABoundedPiOneUnary
import DiophantineConsistency.PRAWitnessTransfer
import DiophantineConsistency.StrictPiTwoBridge

/-!
# From `𝗜𝚺₁` to iPRA for consistency machines

Let `δ` be a `Σ₀` formula of the language of arithmetic in one variable, so that `∃ t, δ t`
is a strict `Σ₁` sentence; the intended reading is "the machine halts, with history `t`".

`endpoint`: if Foundation's `𝗜𝚺₁` proves `paRefutation ↔ ∃ t, δ t`, then standard iPRA proves
`nativePAConsistency ↔ ¬ haltSentence δ`, where `haltSentence δ` is the same sentence mapped
into the language of iPRA and read with intuitionistic connectives.

So for a machine it is enough to prove one equivalence in `𝗜𝚺₁`, by reasoning in arbitrary
models of `𝗜𝚺₁`. Nothing here is specific to a machine, and no machine equivalence is proved.

The proof has two steps.

* `classical_iff`: candidate PRA proves the mapped equivalence. Both sides are brought to the
  form `∀ x, open` (`PRABoundedPiOneUnary.unary_open`), and the `𝗜𝚺₁` proof is transferred by
  `PRAISigmaOneOriginalEquivalence.comparison`, the formalized conservation of `𝗜𝚺₁` over
  candidate PRA for such equivalences. The PA side needs the witness bound `BoundCertificate`
  for Foundation's PA-refutation predicate. That statement is the proposition
  `PA196ReverseGG.BoundCertificate`, which `PA196PACertificateComplete.certificate` proves; it
  is a hypothesis here so that this file does not import a machine.
* `forward`, `reverse`: the two classical implications are carried into iPRA through the
  Gödel–Gentzen translation, as `PA194ForwardGG` and `PA196ReverseGG` do for an atomic halting
  matrix. The lemmas `matrix_all`, `exists_backward` and `refutation_backward` are those of
  these two files, restated without their machine imports.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace ConPA.ISigma1Transfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRAExistentialComparison
open DiophantineConsistency.IPRANativeForwardTheory DiophantineConsistency.IPRANativeDisjunctionWitness
open DiophantineConsistency.StrictSigmaOneInduction
open DiophantineConsistency.IPRARefutationWitnessBridge
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

attribute [local irreducible] paRefutation

/-! ## Classical step -/

/-- The witness bound for Foundation's PA-refutation predicate in candidate PRA. -/
def BoundCertificate : Prop :=
  PRA ⊢ Semiformula.lMap embedding (paRefutation 🡒 ∃⁰ bnd paRefutation)

theorem bnd_paRefutation_sigma_zero : Hierarchy 𝚺 0 (bnd paRefutation) :=
  hierarchy_bnd paRefutation_sigma_one (by decide) (by intro _; rfl)

theorem evalb_all_neg {L : Language} {M : Type*} [Structure L M] (ψ : Semisentence L 1) :
    (∀⁰ ∼ψ).Evalb (M := M) ![] ↔ ∀ x : M, ¬ψ.Eval ![x] Empty.elim := by
  simp [Semiformula.eval_all]

theorem evalb_ex {L : Language} {M : Type*} [Structure L M] (ψ : Semisentence L 1) :
    (∃⁰ ψ).Evalb (M := M) ![] ↔ ∃ x : M, ψ.Eval ![x] Empty.elim := by
  simp [Semiformula.eval_ex]

/-- `𝗜𝚺₁` proves the two strict `Π₁` forms equivalent. -/
theorem isigma1_strict (δ : ArithmeticSemisentence 1)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) :
    𝗜𝚺₁ ⊢ ((∀⁰ ∼bnd paRefutation) 🡘 (∀⁰ ∼δ)) := by
  refine complete.{0} _ _ fun M _ hM => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have hE := models_of_provable hM h
  have hb := DiophantineConsistency.StrictPiTwoBridge.eval_bnd_iff (M := M) paRefutation_sigma_one
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hE ⊢
  have hE1 : paRefutation.Evalb (M := M) ![] → (∃⁰ δ).Evalb (M := M) ![] := hE.1
  have hE2 : (∃⁰ δ).Evalb (M := M) ![] → paRefutation.Evalb (M := M) ![] := hE.2
  constructor
  · intro hall
    have hall' := (evalb_all_neg (bnd paRefutation)).mp hall
    refine (evalb_all_neg δ).mpr ?_
    intro x hx
    obtain ⟨w, hw⟩ := hb.mp (hE2 ((evalb_ex δ).mpr ⟨x, hx⟩))
    exact hall' w hw
  · intro hall
    have hall' := (evalb_all_neg δ).mp hall
    refine (evalb_all_neg (bnd paRefutation)).mpr ?_
    intro w hw
    obtain ⟨x, hx⟩ := (evalb_ex δ).mp (hE1 (hb.mpr ⟨w, hw⟩))
    exact hall' x hx

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
/-- The semantic content of the classical step in one candidate PRA model. -/
theorem model_iff (δ : ArithmeticSemisentence 1)
    (hcmp : M↓[language] ⊧ (Semiformula.lMap embedding (∀⁰ ∼bnd paRefutation) 🡘
      Semiformula.lMap embedding (∀⁰ ∼δ)))
    (hcert : M↓[language] ⊧ Semiformula.lMap embedding (paRefutation 🡒 ∃⁰ bnd paRefutation)) :
    M↓[language] ⊧ (mappedPARefutation 🡘 Semiformula.lMap embedding (∃⁰ δ)) := by
  have std {k : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → M) :
      (Semiformula.lMap embedding φ).Eval v Empty.elim ↔ φ.Eval v Empty.elim :=
    DiophantineConsistency.PRAWitnessTransfer.eval_lMap_std φ v
  have a1 : (M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼bnd paRefutation)) ↔
      ∀ w : M, ¬(bnd paRefutation).Eval ![w] Empty.elim :=
    models_iff.trans ((std (∀⁰ ∼bnd paRefutation) ![]).trans (evalb_all_neg (bnd paRefutation)))
  have a2 : (M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼δ)) ↔
      ∀ x : M, ¬δ.Eval ![x] Empty.elim :=
    models_iff.trans ((std (∀⁰ ∼δ) ![]).trans (evalb_all_neg δ))
  have aP : (M↓[language] ⊧ mappedPARefutation) ↔ paRefutation.Eval (M := M) ![] Empty.elim :=
    models_iff.trans (std paRefutation ![])
  have aH : (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ δ)) ↔ ∃ x : M, δ.Eval ![x] Empty.elim :=
    models_iff.trans ((std (∃⁰ δ) ![]).trans (evalb_ex δ))
  have hC : paRefutation.Eval (M := M) ![] Empty.elim →
      ∃ w : M, (bnd paRefutation).Eval ![w] Empty.elim := by
    intro hp
    have h1 := (std (paRefutation 🡒 ∃⁰ bnd paRefutation) ![]).mp (models_iff.mp hcert)
    simp only [LogicalConnective.HomClass.map_imply] at h1
    exact (evalb_ex (bnd paRefutation)).mp (h1 hp)
  have hD : ∀ w : M, (bnd paRefutation).Eval ![w] Empty.elim →
      paRefutation.Eval (M := M) ![] Empty.elim := by
    intro w hw
    exact eval_bnd_imp (M := M) paRefutation ![] w Empty.elim
      (by rwa [DiophantineConsistency.StrictPiTwoBridge.snoc_nil])
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hcmp ⊢
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := hC (aP.mp hp)
    by_contra hne
    exact (a1.mp (hcmp.2 (a2.mpr (fun x hx => hne (aH.mpr ⟨x, hx⟩))))) w hw
  · intro hh
    obtain ⟨x, hx⟩ := aH.mp hh
    by_contra hne
    exact (a2.mp (hcmp.1 (a1.mpr (fun w hw => hne (aP.mpr (hD w hw)))))) x hx
end models

/-- Candidate PRA proves the mapped equivalence when `𝗜𝚺₁` proves the original one. -/
theorem classical_iff (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    PRA ⊢ (mappedPARefutation 🡘 Semiformula.lMap embedding (∃⁰ δ)) := by
  obtain ⟨p, hp, hpα⟩ :=
    DiophantineConsistency.PRABoundedPiOneUnary.unary_open (bnd paRefutation) bnd_paRefutation_sigma_zero
  obtain ⟨q, hq, hqβ⟩ := DiophantineConsistency.PRABoundedPiOneUnary.unary_open δ hδ
  have hcmp := DiophantineConsistency.PRAISigmaOneOriginalEquivalence.comparison
    (∀⁰ ∼bnd paRefutation) (∀⁰ ∼δ) (isigma1_strict δ h) p q hp hq hpα hqβ
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  exact model_iff δ (models_of_provable hM hcmp) (models_of_provable hM hb)

theorem classical_forward (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    PRA ⊢ (mappedPARefutation 🡒 Semiformula.lMap embedding (∃⁰ δ)) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hm := models_of_provable hM (classical_iff δ hδ h hb)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm ⊢
  exact hm.1

theorem classical_reverse (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    PRA ⊢ (Semiformula.lMap embedding (∃⁰ δ) 🡒 mappedPARefutation) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hm := models_of_provable hM (classical_iff δ hδ h hb)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm ⊢
  exact hm.2

/-! ## Intuitionistic step -/

def matrix (φ : Semisentence language 1) : Semisentenceᵢ language 1 := φᴺ 🡒 native φ

def matrix_all (φ : Semisentence language 1) (hφ : Hierarchy 𝚺 0 φ) :
    nativeTheory ⊢! ∀⁰ matrix φ := by
  have hc : nativeTheory ⊢! ∀⁰* matrix φ := by
    apply closeFamily 1 (matrix φ)
    intro v
    have hv : ![v 0] = v := by
      funext i
      cases i using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
    have h := DiophantineConsistency.IPRABoundedInduction.backward φ hφ ![v 0]
    simpa only [matrix, LogicalConnective.HomClass.map_imply,
      Semiformula.rew_doubleNegation, native_rew, hv] using h
  simpa only [allClosure_succ, allClosure_zero] using hc

def exists_backward (φ : Semisentence language 1) (hφ : Hierarchy 𝚺 0 φ) :
    nativeTheory ⊢! (∃⁰ φ)ᴺ 🡒 ∼∼(∃⁰ native φ) :=
  theoryExistsCompare φ (matrix_all φ hφ)

def boundedPARefutation : Sentence language :=
  Semiformula.lMap embedding (∃⁰ bnd paRefutation)

theorem paBoundedMatrix : Hierarchy 𝚺 0 (Semiformula.lMap embedding (bnd paRefutation)) :=
  DiophantineConsistency.ParsonsHierarchyMap.hierarchy bnd_paRefutation_sigma_zero

def bounded_compare : nativeTheory ⊢! boundedPARefutationᴺ 🡒 ∼∼native boundedPARefutation := by
  simpa only [boundedPARefutation, Semiformula.lMap_exs, native] using
    exists_backward (Semiformula.lMap embedding (bnd paRefutation)) paBoundedMatrix

def bounded_erase : nativeTheory ⊢! native boundedPARefutation 🡒 native mappedPARefutation := by
  have h := DiophantineConsistency.IPRABoundedMappedErasure.existsErasure
    (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) embedding paRefutation
  apply Theoryᵢ.ofHilbert
  simpa only [boundedPARefutation, mappedPARefutation, Semiformula.lMap_emb,
    native_rew, LogicalConnective.HomClass.map_imply] using h

def refutation_backward (hb : BoundCertificate) :
    nativeTheory ⊢! mappedPARefutationᴺ 🡒 ∼∼nativePARefutation := by
  unfold BoundCertificate at hb
  have hclass : PRA ⊢ mappedPARefutation 🡒 boundedPARefutation := by
    simpa only [mappedPARefutation, boundedPARefutation, LogicalConnective.HomClass.map_imply] using hb
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 boundedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical hclass)
  exact backwardOfWitness mappedPARefutation boundedPARefutation
    (Classical.choice hgg) bounded_compare bounded_erase

/-- The halting sentence of iPRA: the strict `Σ₁` sentence `∃ t, δ t`, mapped into the
language of iPRA and read with intuitionistic connectives. -/
def haltSentence (δ : ArithmeticSemisentence 1) : Sentenceᵢ language :=
  native (Semiformula.lMap embedding (∃⁰ δ))

def halt_backward (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ) :
    nativeTheory ⊢! (Semiformula.lMap embedding (∃⁰ δ))ᴺ 🡒 ∼∼haltSentence δ := by
  simpa only [haltSentence, Semiformula.lMap_exs, native] using
    exists_backward (Semiformula.lMap embedding δ)
      (DiophantineConsistency.ParsonsHierarchyMap.hierarchy hδ)

/-- A PA refutation gives, in iPRA, the double negation of halting. -/
theorem forward (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    standardTheory ⊢ nativePARefutation 🡒 ∼∼haltSentence δ := by
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 (Semiformula.lMap embedding (∃⁰ δ))ᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical (classical_forward δ hδ h hb))
  have hnative : nativeTheory ⊢! nativePARefutation 🡒 ∼∼haltSentence δ :=
    Entailment.C_trans (theoryNativeForward mappedPARefutation)
      (Entailment.C_trans (Classical.choice hgg) (halt_backward δ hδ))
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

/-- Halting gives, in iPRA, the double negation of a PA refutation. -/
theorem reverse (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    standardTheory ⊢ haltSentence δ 🡒 ∼∼nativePARefutation := by
  have hgg : nativeTheory ⊢ (Semiformula.lMap embedding (∃⁰ δ))ᴺ 🡒 mappedPARefutationᴺ :=
    DiophantineConsistency.IPRAImpGG.unpack_imp_image nativeTheory _ _
      (DiophantineConsistency.IPRAFullGGTransfer.from_classical (classical_reverse δ hδ h hb))
  have hf : nativeTheory ⊢! haltSentence δ 🡒 (Semiformula.lMap embedding (∃⁰ δ))ᴺ :=
    theoryNativeForward (Semiformula.lMap embedding (∃⁰ δ))
  have hnative : nativeTheory ⊢! haltSentence δ 🡒 ∼∼nativePARefutation :=
    Entailment.C_trans hf (Entailment.C_trans (Classical.choice hgg) (refutation_backward hb))
  exact (DiophantineConsistency.IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

/-- **The transfer.** An `𝗜𝚺₁` proof of `paRefutation ↔ ∃ t, δ t` with `δ` bounded gives the
iPRA equivalence of PA consistency and non-halting. -/
theorem endpoint (δ : ArithmeticSemisentence 1) (hδ : Hierarchy 𝚺 0 δ)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 ∃⁰ δ)) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence δ := by
  have hf := Classical.choice (forward δ hδ h hb)
  have hr := Classical.choice (reverse δ hδ h hb)
  refine ⟨?_⟩
  unfold nativePAConsistency
  exact Entailment.K_intro
    (Entailment.C_trans Entailment.dni (Entailment.contra hr))
    (Entailment.C_trans Entailment.dni (Entailment.contra hf))

/-- The same for an arbitrary `Σ₁` sentence `H`: its strict form `∃ w, bnd H w` is the halting
sentence. In `𝗜𝚺₁` the two are equivalent (`StrictPiTwoBridge.eval_bnd_iff`). -/
theorem endpoint_sigma_one (H : ArithmeticSentence) (hH : Hierarchy 𝚺 1 H)
    (h : 𝗜𝚺₁ ⊢ (paRefutation 🡘 H)) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence (bnd H) := by
  refine endpoint (bnd H) (hierarchy_bnd hH (by decide) (by intro _; rfl)) ?_ hb
  refine complete.{0} _ _ fun M _ hM => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have hE := models_of_provable hM h
  have hb' := DiophantineConsistency.StrictPiTwoBridge.eval_bnd_iff (M := M) hH
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hE ⊢
  have hE1 : paRefutation.Evalb (M := M) ![] → H.Evalb (M := M) ![] := hE.1
  have hE2 : H.Evalb (M := M) ![] → paRefutation.Evalb (M := M) ![] := hE.2
  exact ⟨fun hp => (evalb_ex (bnd H)).mpr (hb'.mp (hE1 hp)),
    fun hh => hE2 (hb'.mpr ((evalb_ex (bnd H)).mp hh))⟩

#print axioms classical_iff
#print axioms endpoint_sigma_one
#print axioms endpoint
end ConPA.ISigma1Transfer
