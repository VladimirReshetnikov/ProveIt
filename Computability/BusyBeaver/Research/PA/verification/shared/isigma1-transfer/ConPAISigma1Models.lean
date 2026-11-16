import ConPAISigma1Transfer
import DiophantineConsistency.PRAModelIOpenPairing

/-!
# Candidate PRA models may be assumed to satisfy `𝗜𝚺₁`

For sentences of the language of candidate PRA of the shapes that the consistency endpoints
use, truth in every candidate PRA model *whose arithmetic reduct satisfies `𝗜𝚺₁`* already
gives provability in candidate PRA.

* `finite_isigma1`: a sentence true in all such models follows in PRA from the image of one
  theorem of `𝗜𝚺₁` (completeness and compactness).
* `open_existential_of_models`, `pi_one_iff_of_models`: with the formalized conservation
  theorems `PRAISigmaOneOpenComparison.comparison` and `PRAISigmaOnePiOneComparison.comparison`
  this gives provability in PRA of `∀ x̄ ∃ y θ` and of `(∀ x p) ↔ (∀ x q)` for open `θ`, `p`, `q`.
  The matrices are formulas of the PRA language and may contain its function symbols.
* `halt_iff_refutation_of_models`, `forward_of_models`, `reverse_of_models`: for an open
  halting matrix `halt` of the PRA language, if in every such model `∃ t, halt t` holds exactly
  when the mapped PA refutation holds, then PRA proves the equivalence and both reductions that
  the endpoints `PA194PRAAssembly` and `PA196PRAAssembly` take as hypotheses.

So a machine reduction may be proved in models of PRA in which, in addition, `Σ₁` induction
and Foundation's internal proof theory of `𝗣𝗔` are available
(`PA194RefutationBridge.mapped_refutation_iff` is stated for exactly these models).
No machine reduction is proved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace ConPA.ISigma1Models
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRATheory
open DiophantineConsistency.IPRAPA196Consistency
open DiophantineConsistency.StrictSigmaOneInduction
open ConPA.ISigma1Transfer

/-- The arithmetic reduct of a structure for the PRA language satisfies `𝗜𝚺₁`. -/
def ReductISigma1 (M : Type) [Nonempty M] [Structure language M] : Prop :=
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁

/-- The theory of the models considered: candidate PRA and the image of `𝗜𝚺₁`. -/
def extended : Theory language :=
  PRA ∪ {a | ∃ τ ∈ (𝗜𝚺₁ : ArithmeticTheory), Semiformula.lMap embedding τ = a}

instance : 𝗘𝗤 language ⪯ extended :=
  Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))

/-- A sentence true in every candidate PRA model with an `𝗜𝚺₁` reduct follows in PRA from the
image of a single theorem of `𝗜𝚺₁`. -/
theorem finite_isigma1 (φ : Sentence language)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M → M↓[language] ⊧ φ) :
    ∃ σ : ArithmeticSentence, 𝗜𝚺₁ ⊢ σ ∧ PRA ⊢ (Semiformula.lMap embedding σ 🡒 φ) := by
  have hT : extended ⊢ φ := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro τ hτ
      exact hBoth.models _ (Or.inl hτ)
    apply h M
    unfold ReductISigma1
    letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
    constructor
    intro τ hτ
    have hm : M↓[language] ⊧ Semiformula.lMap embedding τ := hBoth.models _ (Or.inr ⟨τ, hτ, rfl⟩)
    exact Semiformula.models_lMap.mp hm
  obtain ⟨p⟩ := hT
  classical
  let pre : Sentence language → ArithmeticSentence := fun a =>
    if ha : ∃ τ ∈ (𝗜𝚺₁ : ArithmeticTheory), Semiformula.lMap embedding τ = a
    then Classical.choose ha else ⊤
  have pre_mem : ∀ a, (∃ τ ∈ (𝗜𝚺₁ : ArithmeticTheory), Semiformula.lMap embedding τ = a) →
      pre a ∈ (𝗜𝚺₁ : ArithmeticTheory) ∧ Semiformula.lMap embedding (pre a) = a := by
    intro a ha
    simp only [pre, dif_pos ha]
    exact Classical.choose_spec ha
  refine ⟨(p.axioms.map pre).conj, ?_, ?_⟩
  · refine complete.{0} _ _ fun M _ hM => ?_
    rw [models_iff, List.map_conj_prop]
    intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    by_cases hx : ∃ τ ∈ (𝗜𝚺₁ : ArithmeticTheory), Semiformula.lMap embedding τ = a
    · exact models_iff.mp (hM.models _ (pre_mem a hx).1)
    · simp only [pre, dif_neg hx]
      trivial
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    simp only [Semantics.Imp.models_imply]
    intro hs
    letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
    have hs' : M↓[ℒₒᵣ] ⊧ (p.axioms.map pre).conj := Semiformula.models_lMap.mp hs
    rw [models_iff, List.map_conj_prop] at hs'
    have haxioms : ∀ τ ∈ p.axioms, M↓[language] ⊧ τ := by
      intro a ha
      rcases p.axioms_mem a ha with hpra | hx
      · exact hM.models _ hpra
      · have hb := hs' (pre a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
        have hm : M↓[language] ⊧ Semiformula.lMap embedding (pre a) :=
          Semiformula.models_lMap.mpr (models_iff.mpr hb)
        rwa [(pre_mem a hx).2] at hm
    have hp : Theory.Proof {τ | M↓[language] ⊧ τ} φ := ⟨p.axioms, haxioms, p.derivation⟩
    have hmodel : M↓[language] ⊧* {τ | M↓[language] ⊧ τ} := ⟨fun _ h => h⟩
    exact models_of_provable hmodel ⟨hp⟩

/-- Provability in PRA of `∀ x̄ ∃ y θ` with `θ` open, from truth in the models with an `𝗜𝚺₁`
reduct. -/
theorem open_existential_of_models (θ : Semiproposition language 1) (hθ : θ.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M → M↓[language] ⊧ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  obtain ⟨σ, hσ, hg⟩ := finite_isigma1 _ h
  exact DiophantineConsistency.PRAISigmaOneOpenComparison.comparison σ hσ θ hθ hg

/-- Provability in PRA of `(∀ x p) ↔ (∀ x q)` with `p`, `q` open, from truth in the models
with an `𝗜𝚺₁` reduct. -/
theorem pi_one_iff_of_models (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M → M↓[language] ⊧ ((∀⁰ p) 🡘 (∀⁰ q))) :
    PRA ⊢ ((∀⁰ p) 🡘 (∀⁰ q)) := by
  obtain ⟨σ, hσ, hg⟩ := finite_isigma1 _ h
  exact DiophantineConsistency.PRAISigmaOnePiOneComparison.comparison σ hσ p q hp hq hg

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
/-- With the arithmetic operations read off the PRA structure, the reduct is the standard
structure, so `ReductISigma1 M` is the instance that Foundation's lemmas ask for. -/
theorem standard_isigma1 (hr : ReductISigma1 M) : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := by
  unfold ReductISigma1 at hr
  rw [DiophantineConsistency.PRAModelIOpenPairing.reduct_eq_standard] at hr
  exact hr

omit [M↓[language] ⊧* PRA] in
theorem reduct_of_standard (hs : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁) : ReductISigma1 M := by
  unfold ReductISigma1
  rw [DiophantineConsistency.PRAModelIOpenPairing.reduct_eq_standard]
  exact hs

omit [M↓[language] ⊧* PRA] in
/-- In a candidate PRA model satisfying the certificate, the mapped PA refutation fails
exactly when no bound works. -/
theorem model_refutation (hcert : M↓[language] ⊧
      Semiformula.lMap embedding (paRefutation 🡒 ∃⁰ bnd paRefutation)) :
    (M↓[language] ⊧ mappedPARefutation) ↔
      ¬(M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼bnd paRefutation)) := by
  have std {k : ℕ} (φ : ArithmeticSemisentence k) (v : Fin k → M) :
      (Semiformula.lMap embedding φ).Eval v Empty.elim ↔ φ.Eval v Empty.elim :=
    DiophantineConsistency.PRAWitnessTransfer.eval_lMap_std φ v
  have a1 : (M↓[language] ⊧ Semiformula.lMap embedding (∀⁰ ∼bnd paRefutation)) ↔
      ∀ w : M, ¬(bnd paRefutation).Eval ![w] Empty.elim :=
    models_iff.trans ((std (∀⁰ ∼bnd paRefutation) ![]).trans (evalb_all_neg (bnd paRefutation)))
  have aP : (M↓[language] ⊧ mappedPARefutation) ↔ paRefutation.Eval (M := M) ![] Empty.elim :=
    models_iff.trans (std paRefutation ![])
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
  constructor
  · intro hp hall
    obtain ⟨w, hw⟩ := hC (aP.mp hp)
    exact a1.mp hall w hw
  · intro hne
    by_contra hp
    exact hne (a1.mpr (fun w hw => hp (aP.mpr (hD w hw))))
end models

/-- **Halting and refutation.** For an open halting matrix of the PRA language: if in every
candidate PRA model with an `𝗜𝚺₁` reduct the machine halts exactly when the mapped PA
refutation holds, then PRA proves the equivalence. -/
theorem halt_iff_refutation_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation)))
    (hb : BoundCertificate) :
    PRA ⊢ ((∃⁰ halt) 🡘 mappedPARefutation) := by
  obtain ⟨q, hq, hqα⟩ :=
    DiophantineConsistency.PRABoundedPiOneUnary.unary_open (bnd paRefutation) bnd_paRefutation_sigma_zero
  have hnopen : (∼halt).Open := by simpa using hopen
  have hall (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M] :
      (M↓[language] ⊧ ∀⁰ ∼halt) ↔ ¬(M↓[language] ⊧ ∃⁰ halt) := by
    rw [models_iff, models_iff]
    exact (evalb_all_neg halt).trans
      ⟨fun h hex => by obtain ⟨x, hx⟩ := (evalb_ex halt).mp hex; exact h x hx,
        fun h x hx => h ((evalb_ex halt).mpr ⟨x, hx⟩)⟩
  have hcmp : PRA ⊢ ((∀⁰ ∼halt) 🡘 (∀⁰ q)) := by
    apply pi_one_iff_of_models (∼halt) q hnopen hq
    intro M _ _ _ hM hr
    have hqm := models_of_provable hM hqα
    have hcert := models_of_provable hM hb
    have hmr := model_refutation (M := M) hcert
    have hh := h M hr
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqm ⊢
    constructor
    · intro ha
      by_contra hnq
      have : M↓[language] ⊧ mappedPARefutation := hmr.mpr (fun hx => hnq (hqm.1 hx))
      exact (hall M).mp ha (hh.mpr this)
    · intro hq'
      refine (hall M).mpr ?_
      intro hhalt
      exact (hmr.mp (hh.mp hhalt)) (hqm.2 hq')
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hc := models_of_provable hM hcmp
  have hqm := models_of_provable hM hqα
  have hcert := models_of_provable hM hb
  have hmr := model_refutation (M := M) hcert
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply]
    at hc hqm ⊢
  constructor
  · intro hhalt
    refine hmr.mpr ?_
    intro hx
    exact (hall M).mp (hc.2 (hqm.1 hx)) hhalt
  · intro hp
    by_contra hnh
    exact (hmr.mp hp) (hqm.2 (hc.1 ((hall M).mpr hnh)))

/-- The forward reduction of the endpoints, from truth in the models with an `𝗜𝚺₁` reduct. -/
theorem forward_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation)))
    (hb : BoundCertificate) :
    PRA ⊢ (mappedPARefutation 🡒 ∃⁰ halt) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hm := models_of_provable hM (halt_iff_refutation_of_models halt hopen h hb)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm ⊢
  exact hm.2

/-- The reverse reduction of the endpoints, from truth in the models with an `𝗜𝚺₁` reduct. -/
theorem reverse_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation)))
    (hb : BoundCertificate) :
    PRA ⊢ ((∃⁰ halt) 🡒 mappedPARefutation) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hm := models_of_provable hM (halt_iff_refutation_of_models halt hopen h hb)
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hm ⊢
  exact hm.1

#print axioms finite_isigma1
#print axioms pi_one_iff_of_models
#print axioms halt_iff_refutation_of_models
end ConPA.ISigma1Models
