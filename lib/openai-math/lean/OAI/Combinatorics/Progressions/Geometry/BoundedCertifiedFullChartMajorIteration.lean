import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure CertifiedFullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  certificate : RationalTaggedConstraintCertificate J Kinitial K Bphase
    (n * (Fintype.card η * m))
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

namespace CertifiedFullChartFiniteHistory

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

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

noncomputable def initial
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    State 0 where
  slow := fun _ => 0
  rat := fun _ => 0
  q := fun _ => 1
  K := Kinitial
  certificate := by simpa using RationalTaggedConstraintCertificate.empty (J := J) Kinitial Bphase
  subset := fun _ ht => ht
  dilation := hK
  retained := fun _ ht _ => ht
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_pos := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  rat_grid := fun j hj => (Nat.not_lt_zero j hj).elim
  invariant := by
    dsimp only
    intro t ht j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [F.realSymbolGradeEvaluation_zero]
    exact Submodule.zero_mem _

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

noncomputable def mono_bound {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N B' n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  certificate := H.certificate.monoB hBB'
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := fun j hj α i => (H.slow_bound j hj α i).trans (Real.exp_le_exp.mpr hBB')
  q_pos := H.q_pos
  q_bound := fun j hj => (H.q_bound j hj).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hBB' (Nat.cast_nonneg _)))
  rat_grid := H.rat_grid
  invariant := H.invariant

theorem outer_mono_bound {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    (H.mono_bound hBB').outer = H.outer := by
  dsimp only [outer, mono_bound]

theorem mono_bound_K {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    (H.mono_bound hBB').K = H.K := rfl

theorem invariant_outer {n : ℕ} (H : State n) :
    ∀ t ∈ H.K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
  dsimp only [outer]
  have h := H.invariant
  dsimp only at h
  with_reducible exact h

noncomputable def toUncertified {n : ℕ} (H : State n) :
    FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := H.slow_bound
  q_pos := H.q_pos
  q_bound := H.q_bound
  rat_grid := H.rat_grid
  invariant := H.invariant

@[simp] theorem outer_toUncertified {n : ℕ} (H : State n) :
    FullChartFiniteHistory.outer F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase
      H.toUncertified = H.outer := by
  dsimp only [FullChartFiniteHistory.outer, outer, toUncertified]

@[simp] theorem toUncertified_K {n : ℕ} (H : State n) : H.toUncertified.K = H.K := rfl

theorem exists_step {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase)
    (hdata : CertifiedFullChartGradeCorrectionData F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget) :
    ∃ Hnext : State (n + 1),
      (∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j) ∧
      Hnext.K ⊆ H.K := by
  classical
  unfold CertifiedFullChartGradeCorrectionData at hdata
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid, hnext, _, hcert⟩ := hdata
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
  exact ⟨Hnext, fun j hj => ⟨hslow j hj, hrat j hj, hqold j hj⟩, hsub⟩

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_certified_full_chart_grade_correction_of_major_correlation
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      FullChartMajorCorrelation F b ω hF J k fast basis Z left right D N poly U p Rrank C →
      CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hmatching⟩ := exists_full_restricted_grade_major_matching m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower D htk N poly U p Rrank hcorrelation
  obtain ⟨periodCap, coverCap, Lip, W, R, Ψ, c, β, hpoly, hcoeff, hβ,
    hp, hR, hRcap, hdim, hmod, hcover, hLip, hΨ, hN, hRrank, hrank, hcorr⟩ := hcorrelation
  have hdetected := hmatching F b ω hF J fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower W D htk R N poly hpoly U hcoeff Ψ c β hβ
    p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hchart := fullChartDetectedMajorGradeConclusion_of_fullTagged F b ω hF J k fast
    basis lift Z left right K₀ U poly c N ((p + C) ^ C) hdetected
  exact certifiedFullChartGradeCorrectionData_of_detected F b ω hF J k fast basis lift
    Z left right K₀ U poly N ((p + C) ^ C) c hK₀ hchart

attribute [local instance] FullChartMajorCorrelationWitness.lie
  FullChartMajorCorrelationWitness.algebra FullChartMajorCorrelationWitness.topology
  FullChartMajorCorrelationWitness.topologicalAdd FullChartMajorCorrelationWitness.continuousSMul
  FullChartMajorCorrelationWitness.hausdorff

theorem exists_certified_full_chart_grade_correction_of_major_correlation_witness
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
        Z left right N poly U p Rrank C) →
      CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_certified_full_chart_grade_correction_of_major_correlation m k hk
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower N poly U p Rrank hwitness
  obtain ⟨witness⟩ := hwitness
  exact hstep F b ω hF J fast basis lift hfast hsection Z left right K₀ hK₀ hlower
    witness.model witness.lower N poly U p Rrank witness.correlation

def CertifiedBundledFullChartControlledCorrelationSourceStages
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (pPhase : ℕ → ℝ) (Rrank : ℝ) (Cphase : ℕ → ℕ) (controlBudget constraintBudget : ℕ → ℝ) : Prop :=
  ∀ n < s,
    ∀ (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K : Set (X ⊕ (Σ j, J j) → ℝ)),
      K ⊆ Kinitial →
      (∀ t ∈ K, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K) →
      (∀ t ∈ Kinitial, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      (∀ t ∈ K, ∀ j < n + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ) →
      RationalTaggedConstraintCertificate J Kinitial K (constraintBudget n)
        (n * (Fintype.card η * m)) →
      FullChartControlledFactors F b ω hF J poly N left right (controlBudget n) →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z left right N poly Utag (pPhase n) Rrank (Cphase n))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_bounded_certified_full_chart_major_iteration (m s a : ℕ) :
    ∃ (Cphase : ℕ → ℕ) (Ccontrol : ℕ), (∀ n, 2 ≤ Cphase n) ∧ 2 ≤ Ccontrol ∧
    ∀ {X L ι Γ : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded) (v : Γ → F.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = fast)
      (H : ℕ) (_hHpos : 1 ≤ H)
      (_hv : ∀ i j, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H)
      (p₀ : ℝ) (_hp₀ : 0 ≤ p₀)
      (_hrows : (Fintype.card ι : ℝ) ≤ p₀) (_hcols : (Fintype.card Γ : ℝ) ≤ p₀)
      (_hH : (H : ℝ) ≤ Real.exp p₀)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast),
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
        ∃ (eQ : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ fast))
          (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded) (qS : ℕ),
          Function.RightInverse lift fast.mkQ ∧
          Function.RightInverse (lift.baseChange ℝ) (fast.mkQ.baseChange ℝ) ∧
          0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p₀ + 2) ^ 47) ∧
          (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p₀ + 2) ^ 45)) ∧
          (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
          (∀ j i, RationalHeightLE (((eQ.coord j).comp fast.mkQ)
            (F.associatedGradedBasis b ω hF i)) ⌈Real.exp ((p₀ + 2) ^ 7)⌉₊) ∧
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
        (_hKinitial : ∀ t ∈ Kinitial, ∀ r : ℚ,
          (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ Kinitial)
        (Utag : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (pPhase Bpast : ℕ → ℝ) (Rrank : ℝ) (_hBpast : ∀ n ≤ s, 0 ≤ Bpast n)
        (_hBmono : Monotone Bpast)
        (_hphaseBudget : ∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ Bpast (n + 1))
        (Hcontrol : ℕ) (pControl : ℕ → ℝ),
        1 ≤ Hcontrol → (∀ n ≤ s, 0 ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Hcontrol : ℝ) ≤ Real.exp (pControl n)) →
        (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
          ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) Hcontrol) →
        (∀ n ≤ s, Real.exp ((p₀ + 2) ^ 47) * Real.exp ((s : ℝ) * d * Bpast n) ≤
          Real.exp (pControl n)) →
        (∀ n ≤ s, (d : ℝ) * Real.exp ((p₀ + 2) ^ 45) * Real.exp (Bpast n) ≤
          Real.exp ((pControl n + 2) ^ a)) →
        CertifiedBundledFullChartControlledCorrelationSourceStages F b ω hF J fast (eQ.baseChange ℝ) Z
          Kinitial Utag poly N pPhase Rrank Cphase (fun n => (pControl n + Ccontrol) ^ Ccontrol) Bpast →
        ∃ history : CertifiedFullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
          Z Kinitial Utag poly N (Bpast s) s,
          FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
            ((pControl s + Ccontrol) ^ Ccontrol) ∧
          ∀ t ∈ history.K,
            eval₂ t (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
              (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ := by
  classical
  choose Cphase hCphase hstep using
    (fun n : ℕ => exists_certified_full_chart_grade_correction_of_major_correlation_witness
      m (n + 1) (Nat.zero_lt_succ n))
  obtain ⟨Ccontrol, hCcontrol, hprefix⟩ := exists_restricted_chart_prefix_control s a
  refine ⟨Cphase, Ccontrol, hCphase, hCcontrol, ?_⟩
  intro X L ι Γ _ _ _ _ _ _ F b ω hF J _ fast v hspan H hHpos hv
    p₀ hp₀ hrows hcols hH hfast
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates (F.associatedGradedBasis b ω hF)
      fast v hspan hHpos hv hp₀ hrows hcols hH
  refine ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord, ?_⟩
  intro Z Kinitial hKinitial Utag poly N pPhase Bpast Rrank
    hBpast hBmono hphaseBudget Hcontrol pControl hHcontrol hpControl hι hσ hHexp hstructure
    hdenbudget hcost hsource
  have hcontrol : ∀ n ≤ s,
      ∀ history : CertifiedFullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    intro n hn history
    have hdenbudget' : (qS : ℝ) *
        Real.exp ((s : ℝ) * (Fintype.card (Fin d) : ℝ) * Bpast n) ≤ Real.exp (pControl n) := by
      simpa only [Fintype.card_fin] using
        (mul_le_mul_of_nonneg_right hqSB (Real.exp_nonneg _)).trans (hdenbudget n hn)
    have hcost' : (Fintype.card (Fin d) : ℝ) * Real.exp ((p₀ + 2) ^ 45) *
        Real.exp (Bpast n) ≤ Real.exp ((pControl n + 2) ^ a) := by
      simpa only [Fintype.card_fin] using hcost n hn
    obtain ⟨q, hq, hqB, _hdiv, Echart, hE, hEbound, hRgrid⟩ :=
      hprefix F b ω hF (fullTaggedVariableWeight J) (fullTaggedVariableWeight_pos J)
        Hcontrol (pControl n) hHcontrol (hpControl n hn) (hι n hn) (hσ n hn) (hHexp n hn) hstructure
        fast lift (eQ.baseChange ℝ) (Real.exp ((p₀ + 2) ^ 45)) (Bpast n) qS (hBpast n hn) hqS
        hdenbudget' hcost' hentry hgrid
        (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
        (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ)))
        history.slow history.rat history.q n hn history.q_pos history.q_bound
        history.slow_bound history.rat_grid
    unfold FullChartControlledFactors CertifiedFullChartFiniteHistory.outer
    with_reducible exact ⟨q, hq, hqB, Echart, hE, hEbound, hRgrid⟩
  have hexists : ∀ n ≤ s,
      Nonempty (CertifiedFullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨CertifiedFullChartFiniteHistory.initial F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast 0) hKinitial⟩
    | succ n ih =>
      intro hn
      obtain ⟨history⟩ := ih (by omega)
      have hlower : ∀ t ∈ history.K, ∀ j < n + 1,
          F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
            (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
        intro t ht j hj
        with_reducible exact history.invariant_outer t ht j (by omega)
      have hcorr := hsource n (by omega) history.outer.1 history.outer.2 history.K
        history.subset history.dilation history.retained hlower history.certificate (hcontrol n (by omega) history)
      have hdata := hstep n F b ω hF J fast (eQ.baseChange ℝ) lift hfast hsection
        Z history.outer.1 history.outer.2 history.K history.dilation hlower
        N poly Utag (pPhase n) Rrank hcorr
      let larger := history.mono_bound (hBmono (Nat.le_succ n))
      have hdata' : CertifiedFullChartGradeCorrectionData F b ω hF J (n + 1) fast
          (eQ.baseChange ℝ) lift Z larger.outer.1 larger.outer.2 larger.K Utag poly N
          ((pPhase n + Cphase n) ^ Cphase n) := by
        simpa only [larger, CertifiedFullChartFiniteHistory.outer_mono_bound,
          CertifiedFullChartFiniteHistory.mono_bound_K] using hdata
      obtain ⟨next, _⟩ := larger.exists_step ((pPhase n + Cphase n) ^ Cphase n)
        (hphaseBudget n (by omega)) hdata'
      exact ⟨next⟩
  obtain ⟨history⟩ := hexists s le_rfl
  refine ⟨history, hcontrol s le_rfl history, ?_⟩
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF (fullTaggedVariableWeight J)
    fast hfast _ t).mpr
  with_reducible exact history.invariant_outer t ht

end Erdos3.NilpotentLieFiltration

end

end OAI
