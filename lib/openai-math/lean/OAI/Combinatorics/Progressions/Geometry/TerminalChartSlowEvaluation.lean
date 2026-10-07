import Mathlib.RingTheory.MvPolynomial.Tower
import OAI.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
import OAI.Combinatorics.Progressions.Geometry.BoundedCertifiedFullChartMajorIteration
import OAI.Combinatorics.Progressions.Geometry.GlobalMarkedChartwiseNormalization
import OAI.Combinatorics.Progressions.Linear.CertifiedChartBasisBudget
import OAI.Combinatorics.Progressions.Polynomial.FullChartPrescribedPolynomialLifts

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def FullChartAdmissibleStageCorrection
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal) : Prop :=
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.1 α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.2 α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.1).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.2).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pair.1 α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pair.2 α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pair.1))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pair.2 * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pair.1 = lowTaggedVectorExtend J k slow ∧ pair.2 = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pair.1) + eval₂ t pair.2

theorem CertifiedFullChartDetectedDecomposition.exists_admissible_stage
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
      (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
        VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal),
      FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
        Z left right K₀ Utag poly N budget q K' pair := by
  obtain ⟨pS, pR, q, K', hpair⟩ := CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (F := F) (b := b) (ω := ω) (hF := hF) (fast := fast) (lift := lift)
    (J := J) (k := k) (basis := basis) (Z := Z) (left := left) (right := right)
    (K₀ := K₀) (Utag := Utag) (poly := poly) (N := N) (budget := budget) h
  refine ⟨q, K', (pS, pR), ?_⟩
  unfold FullChartAdmissibleStageCorrection
  with_reducible exact hpair

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial outer

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem exists_append_admissible {n : ℕ} (H : State n)
    (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
    (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    ∃ Hnext : State (n + 1),
      Hnext.slow = Function.update H.slow n pair.1 ∧
      Hnext.rat = Function.update H.rat n pair.2 ∧
      Hnext.q = Function.update H.q n q ∧ Hnext.K = K' := by
  let pS := pair.1
  let pR := pair.2
  have hq := hpair.2.2.2.2.1
  have hqB := hpair.2.2.2.2.2.1
  have hsub := hpair.2.2.2.2.2.2.1
  have hdilate := hpair.2.2.2.2.2.2.2.1
  have hretain := hpair.2.2.2.2.2.2.2.2.1
  have hcap := hpair.2.2.2.2.2.2.2.2.2.1
  have hgrid := hpair.2.2.2.2.2.2.2.2.2.2.1
  have hnext := hpair.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert := hpair.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let slow' := Function.update H.slow n pS
  let rat' := Function.update H.rat n pR
  let q' := Function.update H.q n q
  have hslow (j : ℕ) (hj : j < n) : slow' j = H.slow j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hrat (j : ℕ) (hj : j < n) : rat' j = H.rat j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hqold (j : ℕ) (hj : j < n) : q' j = H.q j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hprefix : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' n = H.outer := by
    unfold outer
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      rw [hslow j hj]
    · exact hrat
  have houter : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' (n + 1) =
      (H.outer.1 * F.restrictedMajorCorrection b ω hF wt fast lift (n + 1)
        (realChartSubstitute chart pS),
       F.restrictedMajorCorrection b ω hF wt fast lift (n + 1) pR * H.outer.2) := by
    rw [restrictedMajorOuterFactors, hprefix]
    simp only [slow', rat', Function.update_self]
  have hcapB : ∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp Bphase :=
    fun α i => (hcap α i).trans (Real.exp_le_exp.mpr hbudget)
  have hqBB : (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase) :=
    hqB.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  let Hnext : State (n + 1) := {
    slow := slow'
    rat := rat'
    q := q'
    K := K'
    certificate := by
      simpa only [Nat.succ_mul] using H.certificate.trans (hcert.monoB hbudget)
    subset := fun t ht => H.subset (hsub ht)
    dilation := hdilate
    retained := fun t ht hU => hretain t (H.retained t ht hU) hU
    slow_bound := by
      intro j hj α i
      by_cases hjn : j = n
      · subst j
        simpa only [slow', Function.update_self] using hcapB α i
      · rw [hslow j (by omega)]
        exact H.slow_bound j (by omega) α i
    q_pos := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hq
      · rw [hqold j (by omega)]
        exact H.q_pos j (by omega)
    q_bound := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hqBB
      · rw [hqold j (by omega)]
        exact H.q_bound j (by omega)
    rat_grid := by
      intro j hj α
      by_cases hjn : j = n
      · subst j
        simpa only [rat', q', Function.update_self] using hgrid α
      · rw [hrat j (by omega), hqold j (by omega)]
        exact H.rat_grid j (by omega) α
    invariant := by
      dsimp only
      rw [houter]
      with_reducible exact hnext }
  exact ⟨Hnext, rfl, rfl, rfl, rfl⟩

noncomputable def append_admissible {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) : State (n + 1) :=
  Classical.choose (exists_append_admissible H budget hbudget q K' pair hpair)

@[simp] theorem append_admissible_slow
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow =
      Function.update H.slow n pair.1 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).1

@[simp] theorem append_admissible_rat
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).rat =
      Function.update H.rat n pair.2 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.1

@[simp] theorem append_admissible_q
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).q =
      Function.update H.q n q :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.1

theorem append_admissible_K
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).K = K' :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.2

theorem append_admissible_prefix
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) (j : ℕ) (hj : j < n) :
    (H.append_admissible budget hbudget q K' pair hpair).slow j = H.slow j ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat j = H.rat j ∧
    (H.append_admissible budget hbudget q K' pair hpair).q j = H.q j := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_of_ne (Nat.ne_of_lt hj), and_self]

@[simp] theorem append_admissible_entry
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow n = pair.1 ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat n = pair.2 ∧
    (H.append_admissible budget hbudget q K' pair hpair).q n = q := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_self, and_self]

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

theorem exists_fullChart_admissible_stage_branches
    {past p : ℝ} {blocks : ℕ}
    (hprevious : RationalTaggedConstraintCertificate J Set.univ K₀ past blocks)
    (hp : 0 ≤ p) (hpast : past ≤ p) (hbudget : budget ≤ p)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : ((blocks + Fintype.card η * m : ℕ) : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8) ∧
      ∃ branches : Fin n → ℕ × Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, 0 < (branches i).1 ∧
          (branches i).1 ≤ ⌊Real.exp ((Fintype.card η : ℝ) * budget)⌋₊ ∧
          RationalTaggedConstraintCertificate J Set.univ (branches i).2 p
            (blocks + Fintype.card η * m)) ∧
        ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' pair →
          ∃ i, branches i = (q, K') := by
  obtain ⟨n, hn, branches, hvalid, hcover⟩ :=
    exists_finite_rational_stage_branches Set.univ p ((Fintype.card η : ℝ) * budget)
      hp (blocks + Fintype.card η * m) hm hJ hblocks
  refine ⟨n, hn, branches, hvalid, ?_⟩
  intro q K' pair hpair
  rcases hpair with ⟨_, _, _, _, hq, hqB, _, _, _, _, _, _, _, hcertificate, _⟩
  exact hcover q K' hq hqB
    ((hprevious.monoB hpast).trans (hcertificate.monoB hbudget))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem FullChartAdmissibleStageCorrection.mono_budget
    {m : ℕ} {X : Type} {ι L η : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    {J : Fin m → Type} [∀ j, Fintype (J j)] {k : ℕ}
    {fast : Submodule ℚ F.AssociatedGraded}
    {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
    {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
    {Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    {K₀ : Set (X ⊕ (Σ j, J j) → ℝ)}
    {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
    {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ}
    {budget budget' : ℝ} {q : ℕ} {K' : Set (X ⊕ (Σ j, J j) → ℝ)}
    {pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
    (h : FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget q K' pair)
    (hle : budget ≤ budget') :
    FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget' q K' pair := by
  obtain ⟨hShom, hRhom, hSdeg, hRdeg, hq, hqbound, hsub, hdilation, hretain,
    hslow, hgrid, hnext, horigin, hcertificate, hidentity⟩ := h
  refine ⟨hShom, hRhom, hSdeg, hRdeg, hq, ?_, hsub, hdilation, hretain,
    ?_, hgrid, hnext, horigin, hcertificate.monoB hle, hidentity⟩
  · exact hqbound.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (Fintype.card η))))
  · exact fun α i => (hslow α i).trans (Real.exp_le_exp.mpr hle)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

noncomputable def fullChartStageCountConstant (k a : ℕ) : ℕ :=
  Classical.choose (exists_finite_primitive_correction_budget k a)

theorem fullChartStageCountConstant_ge_two (k a : ℕ) :
    2 ≤ fullChartStageCountConstant k a :=
  (Classical.choose_spec (exists_finite_primitive_correction_budget k a)).1

private theorem certified_basis_envelope {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 254 ≤ a) :
    Real.exp (((p + 2) ^ 2 + 2) ^ 63) ≤ Real.exp ((p + a) ^ a) ∧
      Real.exp ((p + 2) ^ 254) ≤ Real.exp ((p + a) ^ a) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hshift : p + 2 ≤ p + a := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 2 ≤ a by omega)
    linarith
  have hpow (n : ℕ) (hn : n ≤ a) : (p + 2) ^ n ≤ (p + a) ^ a :=
    (pow_le_pow_right₀ hbase hn).trans (pow_le_pow_left₀ (by positivity) hshift a)
  refine ⟨Real.exp_le_exp.mpr ?_, Real.exp_le_exp.mpr (hpow 254 ha)⟩
  exact (show ((p + 2) ^ 2 + 2) ^ 63 ≤ (p + 2) ^ 252 by
    simpa using shifted_power_budget_le hp 2 63).trans (hpow 252 (by omega))

private theorem vector_correction_cover_on_set
    {A B V α : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (Kbase : Submodule ℝ (B → ℝ)) (K : Set (A ⊕ B → ℝ))
    (hset : K = {t | (fun z => t (Sum.inr z)) ∈ Kbase})
    (f₁ f₂ f₃ : α → VectorPolynomial (A ⊕ B) ℚ V)
    (admissible : α → Prop) {count : ℕ} (candidate : Fin count → α)
    (hcover : ∀ a, admissible a → ∃ j, ∀ (u : A → ℝ) (v : B → ℝ), v ∈ Kbase →
      eval₂ (Sum.elim u v) (f₁ (candidate j)) = eval₂ (Sum.elim u v) (f₁ a) ∧
      eval₂ (Sum.elim u v) (f₂ (candidate j)) = eval₂ (Sum.elim u v) (f₂ a) ∧
      eval₂ (Sum.elim u v) (f₃ (candidate j)) = eval₂ (Sum.elim u v) (f₃ a)) :
    ∀ a, admissible a → ∃ j, ∀ t ∈ K,
      eval₂ t (f₁ (candidate j)) = eval₂ t (f₁ a) ∧
      eval₂ t (f₂ (candidate j)) = eval₂ t (f₂ a) ∧
      eval₂ t (f₃ (candidate j)) = eval₂ t (f₃ a) := by
  intro a ha
  obtain ⟨j, hj⟩ := hcover a ha
  refine ⟨j, ?_⟩
  intro t ht
  have ht' : (fun z => t (Sum.inr z)) ∈ Kbase := by
    rw [hset] at ht
    exact ht
  have h := hj (fun i => t (Sum.inl i)) (fun z => t (Sum.inr z)) ht'
  have heq : Sum.elim (fun i => t (Sum.inl i)) (fun z => t (Sum.inr z)) = t := by
    funext i
    cases i <;> rfl
  simpa only [heq] using h

theorem exists_full_chart_finite_stage_representatives [Fintype X]
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (p : ℝ) (blocks a : ℕ) (ha : 254 ≤ a)
    (hcert : RationalTaggedConstraintCertificate J Set.univ K' p blocks)
    (hp : 0 ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p) (hblocks : (blocks : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K')
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) (hq : 0 < q)
    (hqcap : (q : ℝ) ≤ Real.exp ((p + a) ^ a))
    (hbudget : budget ≤ (p + a) ^ a) :
    ∃ count : ℕ, (count : ℝ) ≤
        Real.exp ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin count →
        (VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal),
        (∀ j, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' (candidate j)) ∧
        ∀ pair, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' pair →
          ∃ j, ∀ t ∈ K',
            eval₂ t (candidate j).1 = eval₂ t pair.1 ∧
            eval₂ t (candidate j).2 = eval₂ t pair.2 ∧
            eval₂ t (realChartSubstitute chart (candidate j).1) =
              eval₂ t (realChartSubstitute chart pair.1) := by
  obtain ⟨n, Kbase, e, matrix, d, _, hdim, _, _, _, _, he, _, hd, hdCap, hegrid, hset, hret⟩ :=
    hcert.exists_certified_chart_basis_budget hp hJ hblocks
  let L := Real.exp (((p + 2) ^ 2 + 2) ^ 63)
  let M := Real.exp budget
  let admissible := FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
    Z left right K₀ Utag poly N budget q K'
  have hA := fullTaggedMajorTopCoordinates_coefficients_mem J poly Utag hpoly Kbase
    (hret Utag hretained)
  have hdegree : ∀ pair, admissible pair → ∀ i,
      (coordinate (basis.coord i).toAddMonoidHom pair.1).totalDegree ≤ k ∧
      (coordinate (basis.coord i).toAddMonoidHom pair.2).totalDegree ≤ k := by
    intro pair h i
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact ⟨h.2.2.1 i, h.2.2.2.1 i⟩
  have hcap : ∀ pair, admissible pair → ∀ i ex,
      |basis.coord i (coefficients pair.1 ex)| ≤ M := by
    intro pair h i ex
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact h.2.2.2.2.2.2.2.2.2.1 ex i
  have hgrid : ∀ pair, admissible pair → ∀ ex,
      (fun i => basis.coord i (coefficients pair.2 ex)) ∈ realDenominatorGrid q := by
    intro pair h ex
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact h.2.2.2.2.2.2.2.2.2.2.1 ex
  have hidentity : ∀ pair, admissible pair → ∀ (u : X → ℝ) (v : (Σ j, J j) → ℝ),
      v ∈ Kbase → eval₂ (Sum.elim u v)
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ (Sum.elim u v) (realChartSubstitute chart pair.1) + eval₂ (Sum.elim u v) pair.2 := by
    intro pair h u v hv
    unfold admissible FullChartAdmissibleStageCorrection at h
    have ht : Sum.elim u v ∈ K' := by
      rw [hset]
      exact hv
    with_reducible exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Sum.elim u v) ht
  obtain ⟨count, hcount, candidate, hvalid, hcover⟩ := exists_finite_vector_correction_representatives
    Kbase e basis (fun i => (N i : ℝ)) (fun i => by exact_mod_cast hN i)
    (fullTaggedMajorTopCoordinates J poly) hA
    (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)
    k q d hq hd L M (Real.exp_nonneg budget) he hegrid
    Prod.fst Prod.snd admissible hdegree hcap hgrid hidentity
  refine ⟨count, ?_, candidate, hvalid, ?_⟩
  · have hI : (Fintype.card (Σ j, Fin (n j)) : ℝ) ≤ p :=
      (Nat.cast_le.mpr hdim).trans hJ
    have henvelope := certified_basis_envelope hp ha
    have hcountbudget :=
      (Classical.choose_spec (exists_finite_primitive_correction_budget k a)).2
        (Fintype.card X) (Fintype.card (Σ j, J j)) (Fintype.card (Σ j, Fin (n j)))
        (Fintype.card η) q d p L M hp hX hJ hI hη hqcap
        (hdCap.trans henvelope.2) henvelope.1 (Real.exp_nonneg budget)
        (Real.exp_le_exp.mpr hbudget)
    apply (Nat.cast_le.mpr hcount).trans
    simpa only [Fintype.card_sum, fullChartStageCountConstant] using hcountbudget
  · with_reducible
      exact vector_correction_cover_on_set (V := quotientReal) Kbase K' hset Prod.fst Prod.snd
        (fun pair => realChartSubstitute chart pair.1) admissible candidate hcover

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial outer realChartSubstitute

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

structure StageBounds (cap cumulative : ℕ → ℝ) {n : ℕ} (H : State n) : Prop where
  certificate : RationalTaggedConstraintCertificate J Kinitial H.K (cumulative n)
    (n * (Fintype.card η * m))
  slow_bound : ∀ j < n, ∀ α i,
    |basis.coord i (coefficients (H.slow j) α)| ≤ Real.exp (cap j)
  q_bound : ∀ j < n, (H.q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * cap j)

theorem StageBounds.initial (cap cumulative : ℕ → ℝ)
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    StageBounds cap cumulative
      (initial F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase hK) where
  certificate := by
    unfold CertifiedFullChartFiniteHistory.initial
    simpa only [Nat.zero_mul] using
      RationalTaggedConstraintCertificate.empty (J := J) Kinitial (cumulative 0)
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim

theorem StageBounds.of_admissible_child {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (Hnext : State (n + 1))
    (hprefix : ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) (Hnext.q n) Hnext.K
        (Hnext.slow n, Hnext.rat n))
    (hmono : cumulative n ≤ cumulative (n + 1)) (hcap : cap n ≤ cumulative (n + 1)) :
    StageBounds cap cumulative Hnext := by
  have hcoeff := hpair.2.2.2.2.2.2.2.2.2.1
  have hq := hpair.2.2.2.2.2.1
  have hcert := hpair.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.succ_mul] using
      (hH.certificate.monoB hmono).trans (hcert.monoB hcap)
  · intro j hj α i
    by_cases h : j = n
    · subst j
      exact hcoeff α i
    · rw [(hprefix j (by omega)).1]
      exact hH.slow_bound j (by omega) α i
  · intro j hj
    by_cases h : j = n
    · subst j
      exact hq
    · rw [(hprefix j (by omega)).2.2]
      exact hH.q_bound j (by omega)

noncomputable def StageBounds.to_budget {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (hcap : ∀ j < n, cap j ≤ cumulative n) :
    CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N
      (cumulative n) n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  certificate := hH.certificate
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := fun j hj α i => (hH.slow_bound j hj α i).trans (Real.exp_le_exp.mpr (hcap j hj))
  q_pos := H.q_pos
  q_bound := fun j hj => (hH.q_bound j hj).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcap j hj) (Nat.cast_nonneg _)))
  rat_grid := H.rat_grid
  invariant := H.invariant

theorem StageBounds.to_budget_K {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (hcap : ∀ j < n, cap j ≤ cumulative n) : (hH.to_budget hcap).K = H.K := rfl

theorem StageBounds.to_budget_outer {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (hcap : ∀ j < n, cap j ≤ cumulative n) :
    outer F b ω hF J fast basis lift Z Kinitial Utag poly N (cumulative n)
      (hH.to_budget hcap) = H.outer := by
  unfold outer
  apply F.restrictedMajorOuterFactors_congr
  · intro j hj
    unfold StageBounds.to_budget
    rfl
  · intro j hj
    unfold StageBounds.to_budget
    rfl

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial CertifiedFullChartFiniteHistory.outer
  FullChartControlledFactors

theorem exists_certified_full_chart_history_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X ι η L : Type} [Fintype X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {m : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase B p : ℝ) (H qS : ℕ) (n : ℕ),
      1 ≤ H → 0 ≤ p → 0 ≤ Bphase → 0 < qS → n ≤ s →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * Bphase) ≤ Real.exp p →
      (Fintype.card η : ℝ) * B * Real.exp Bphase ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i) ∈ realDenominatorGrid qS) →
      ∀ history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
        Z Kinitial Utag poly N Bphase n,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((p + C) ^ C) := by
  obtain ⟨C, hC, hprefix⟩ := exists_restricted_chart_prefix_control s a
  refine ⟨C, hC, ?_⟩
  intro X ι η L _ _ _ _ _ m F b ω hF J _ fast basis lift Z Kinitial Utag poly N
    Bphase B p H qS n hH hp hBphase hqS hn hι hσ hHp hstructure hden hcost hentry hgrid history
  obtain ⟨q, hq, hqbound, _, Echart, hE, hEbound, hRgrid⟩ :=
    hprefix F b ω hF (fullTaggedVariableWeight J) (fullTaggedVariableWeight_pos J)
      H p hH hp hι hσ hHp hstructure fast lift basis B Bphase qS hBphase hqS
      hden hcost hentry hgrid
      (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ)))
      history.slow history.rat history.q n hn history.q_pos history.q_bound
      history.slow_bound history.rat_grid
  unfold FullChartControlledFactors CertifiedFullChartFiniteHistory.outer
  with_reducible exact ⟨q, hq, hqbound, Echart, hE, hEbound, hRgrid⟩

namespace CertifiedFullChartFiniteHistory
variable {X ι η L : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s m : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}

  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

theorem terminal_mem_fast
    (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
      Z Kinitial Utag poly N Bphase s)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast) :
    ∀ t ∈ history.K,
      eval₂ t (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
        (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ := by
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF (fullTaggedVariableWeight J)
    fast hfast _ t).mpr
  with_reducible exact history.invariant_outer t ht

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype η] [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem globalRestriction_terminal_mem_pointwise
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
      Z Kinitial Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (β : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE wt (wt i))
    (g : (F.realification.adaptedPolynomialFiltration wt).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF wt g = Z)
    (htop : ∀ t : X ⊕ (Σ j, J j) → ℝ,
      (fun i => MvPolynomial.eval t (weightedHomogeneousComponent wt (wt i) (β i))) ∈ history.K) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF wt wt
      (fun i => weightedHomogeneousComponent wt (wt i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    ((pull history.outer.1)⁻¹ *
      F.realPolynomialSymbolHom b ω hF wt (F.weightedAdaptedRealChartHom wt wt β hβ g) *
      (pull history.outer.2)⁻¹).coord ∈
        realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF wt W) := by
  intro pull
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF wt wt β hβ g, hZ]
  change ((pull history.outer.1)⁻¹ * pull Z * (pull history.outer.2)⁻¹).coord ∈ _
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact F.realSymbolHomogeneousPullback_mem_of_range b ω hF wt wt _ _ W history.K _
    (history.terminal_mem_fast hW) htop

theorem nonempty_globalMarkedNativeFactors [Fintype ι]
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
      Z Kinitial Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (β : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE wt (wt i))
    (g : (F.realification.adaptedPolynomialFiltration wt).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF wt g = Z)
    (htop : ∀ t : X ⊕ (Σ j, J j) → ℝ,
      (fun i => MvPolynomial.eval t (weightedHomogeneousComponent wt (wt i) (β i))) ∈ history.K) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF wt wt
      (fun i => weightedHomogeneousComponent wt (wt i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    Nonempty (GlobalMarkedNativeFactors F b ω hF wt W
      (F.weightedAdaptedRealChartHom wt wt β hβ g)
      (pull history.outer.1) (pull history.outer.2)) := by
  intro pull
  exact F.nonempty_globalMarkedNativeFactors b ω hF wt W _ _ _
    (fullTaggedVariableWeight_pos J)
    (history.globalRestriction_terminal_mem_pointwise hW β hβ g hZ htop)

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute
  symbolPointwiseSubalgebra realificationLieSubalgebra
  PolynomialRationalGrid PolynomialSlowBound

theorem exists_controlled_terminal_globalMarkedNativeFactors (s a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {X ι η L : Type} [Fintype X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (W : LieSubalgebra ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded)
      (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase budget : ℝ)
      (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
        Z Kinitial Utag poly N Bphase s),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2 budget →
    ∀ (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE
        (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J i))
      (_hδ : ∀ i, δ i ∈ weightedSupportLE
        (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J i)),
      (∀ i, weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
        (fullTaggedVariableWeight (X := X) J i) (δ i) =
        MvPolynomial.aeval
          (fun j => weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J j) (β j))
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly) i)) →
      (∀ t : X ⊕ (Σ j, J j) → ℝ,
        (fun i => MvPolynomial.eval t
          (weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J i) (β i))) ∈ history.K) →
    ∀ (D H : ℕ) (p : ℝ), 0 < D → 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → Real.exp budget * (D : ℝ) ^ s ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i, realPolynomialCoefficientGrid D
        (weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
          (fullTaggedVariableWeight (X := X) J i) (β i))) →
      ∃ q n : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < n ∧ (n : ℝ) ≤ Real.exp ((p + Cr) ^ Cr) ∧ q * D ^ s ∣ n ∧
        ∀ g : (F.realification.adaptedPolynomialFiltration
          (fullTaggedVariableWeight (X := X) J)).Group,
        F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight (X := X) J) g = Z →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF
          (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J)
          (fun i => weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J i) (β i))
          (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∃ A : GlobalMarkedNativeFactors F b ω hF (fullTaggedVariableWeight (X := X) J) W
          (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J) β hβ g)
          (pull history.outer.1) (pull history.outer.2),
          F.PolynomialRationalGrid b (fullTaggedVariableWeight (X := X) J) n A.right ∧
          ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card τ : ℝ) ≤ p →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (fullTaggedVariableWeight (X := X) J i))
              (T : τ → ℝ), (∀ i, 0 < T i) →
            ∀ B : ℝ, 1 ≤ B →
              (∀ i, realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
                Real.exp budget * B ^ s ≤ Real.exp ((p + 2) ^ a)) →
              F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
                (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight (X := X) J)
                  v γ hγ A.left) := by
  obtain ⟨Ce, Cr, hCe, hCr, hnormalize⟩ :=
    exists_chartwise_controlled_globalMarkedNativeFactors s a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m X ι η L _ _ _ _ _ F b ω hF J _ W basis lift Z Kinitial Utag poly N
    Bphase budget history hW hcontrol β δ hβ hδ hδtop htop D H p hD hH hp
    hι hσ hHp hden hbracket hgrid
  let w := fullTaggedVariableWeight (X := X) J
  let βtop := fun i => weightedHomogeneousComponent w (w i) (β i)
  have hβtop : ∀ i, (βtop i).IsWeightedHomogeneous w (w i) :=
    fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w w βtop hβtop
  obtain ⟨q, hq, hqB, e₀, r₀, he₀, hr₀, hrGrid, hl, heSlow⟩ :=
    FullChartControlledFactors.exists_prescribed_full_lifts F b ω hF J poly N
      history.outer.1 history.outer.2 hcontrol w βtop δ hβtop hδ hδtop D hD hgrid
  have hlp : ((q * D ^ s : ℕ) : ℝ) ≤ Real.exp p := by
    calc
      ((q * D ^ s : ℕ) : ℝ) = (q : ℝ) * (D : ℝ) ^ s := by simp only [Nat.cast_mul, Nat.cast_pow]
      _ ≤ Real.exp budget * (D : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hqB (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ Real.exp p := hden
  obtain ⟨n, hn, hnp, hln, hfactor⟩ := hnormalize F b ω hF w
    (fullTaggedVariableWeight_pos J) H (q * D ^ s) p hH hl hp hι hσ hHp hlp hbracket
  refine ⟨q, n, hq, hqB, hn, hnp, hln, ?_⟩
  intro g hZ
  change ∃ A : GlobalMarkedNativeFactors F b ω hF w W
      (F.weightedAdaptedRealChartHom w w β hβ g)
      (pull history.outer.1) (pull history.outer.2), _
  have hfast := history.globalRestriction_terminal_mem_pointwise hW β hβ g hZ htop
  change ((pull history.outer.1)⁻¹ *
    F.realPolynomialSymbolHom b ω hF w (F.weightedAdaptedRealChartHom w w β hβ g) *
    (pull history.outer.2)⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) at hfast
  have hresult := hfactor W
    (F.weightedAdaptedRealChartHom w w β hβ g) e₀ r₀
    (pull history.outer.1) (pull history.outer.2) he₀ hr₀ hfast hrGrid
  apply Exists.elim hresult
  intro A hA
  refine ⟨A, hA.1, ?_⟩
  intro τ _ v hv hτ γ hγ T hT B hB hmass hbudget
  apply hA.2 v hv hτ γ hγ T hT
  exact F.polynomialSlowBound_mono b v T hT hbudget _
    (heSlow v γ hγ T hT B hB hmass)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_constant_specialization {σ τ : Type*}
    (T : τ → ℝ) (x : σ → ℝ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ)) P)) =
      |MvPolynomial.eval x P| := by
  have hC : MvPolynomial.aeval (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ)) P =
      MvPolynomial.C (MvPolynomial.eval x P) := by
    simpa only [Function.comp_def, MvPolynomial.aeval_eq_eval] using
      (MvPolynomial.aeval_C_comp_left (R := ℝ) x P :
        MvPolynomial.aeval (MvPolynomial.C (σ := τ) ∘ x) P =
          MvPolynomial.C (MvPolynomial.aeval x P))
  rw [hC]
  have hscale : scaleMvPolynomialAxes T (MvPolynomial.C (MvPolynomial.eval x P)) =
      MvPolynomial.C (MvPolynomial.eval x P) := by
    apply MvPolynomial.funext
    intro y
    rw [scaleMvPolynomialAxes_eval, MvPolynomial.eval_C, MvPolynomial.eval_C]
  rw [hscale, realPolynomialMass_C]

namespace NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
    (w : σ → ℕ)

theorem weightedAdaptedRealChartHom_constantChart
    (v : τ → ℕ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v
      (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ))
      (fun i => weightedSupportLE_C v (w i) (x i)) g =
      F.realification.adaptedConstantGroupHom v
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.weightedAdaptedRealChartHom_coord, F.realification.adaptedConstantGroupHom_log]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, eval₂_realChartSubstitute, MvPolynomial.eval_C,
    VectorPolynomial.eval₂_monomial, Finsupp.prod_zero_index, one_smul,
    F.adaptedPolynomialRealValueHom_coord, sub_self]

theorem polynomialSlowBound_constantChart_value
    (v : τ → ℕ) (T : τ → ℝ) (bound : ℝ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hslow : F.PolynomialSlowBound b v T bound
      (F.weightedAdaptedRealChartHom w v
        (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ))
        (fun i => weightedSupportLE_C v (w i) (x i)) g)) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w x g).coord i| ≤ bound := by
  rw [F.weightedAdaptedRealChartHom_constantChart] at hslow
  simpa only [F.realification.adaptedConstantGroupHom_log, coefficients_monomial,
    Finsupp.single_eq_same, monomialScale_zero, div_one] using hslow 0 i

theorem value_bound_of_terminal_chart_control [Fintype σ]
    (δ : σ → MvPolynomial σ ℝ) (p budget : ℝ) (a Ce : ℕ) (hp : 0 ≤ p)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hcharts : ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
      (Fintype.card τ : ℝ) ≤ p →
      ∀ (γ : σ → MvPolynomial τ ℝ)
        (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
        (T : τ → ℝ), (∀ i, 0 < T i) →
      ∀ mass : ℝ, 1 ≤ mass →
        (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
          (MvPolynomial.aeval γ (δ i))) ≤ mass) →
        (((Fintype.card σ : ℝ) + 1) ^ s * Real.exp budget * mass ^ s ≤
          Real.exp ((p + 2) ^ a)) →
        F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
          (F.weightedAdaptedRealChartHom w v γ hγ g))
    (x : σ → ℝ) (mass : ℝ) (hmass : 1 ≤ mass)
    (hpoint : ∀ i, |MvPolynomial.eval x (δ i)| ≤ mass)
    (hbudget : ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp budget * mass ^ s ≤
      Real.exp ((p + 2) ^ a)) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w x g).coord i| ≤
      Real.exp ((p + Ce) ^ Ce) := by
  apply F.polynomialSlowBound_constantChart_value b w (fun _ : PEmpty => 1)
    (fun _ => 1) _ x g
  apply hcharts (fun _ : PEmpty => 1) (fun i => PEmpty.elim i)
    (by simpa only [Fintype.card_pempty, Nat.cast_zero] using hp)
    (fun i => MvPolynomial.C (x i))
    (fun i => weightedSupportLE_C (fun _ : PEmpty => 1) (w i) (x i))
    (fun _ => 1) (fun i => PEmpty.elim i) mass hmass
    (fun i => ?_) hbudget
  simpa only [realPolynomialMass_constant_specialization] using hpoint i

end NilpotentLieFiltration
end Erdos3

end

end OAI
