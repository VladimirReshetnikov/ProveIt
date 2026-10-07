import OAI.Combinatorics.Progressions.Estimates.AllocatedSourceNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def canonicalProjectionRowCost (m dim : ℕ) : ℕ :=
  Fintype.card (Finset (Fin dim)) *
    ∑ j : Fin m, Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1))

noncomputable def allocatedCanonicalProjectionLog (m dim : ℕ) (P coverLog : ℝ) : ℝ :=
  allocatedFourierLogBudget m P + coverLog + canonicalProjectionRowCost m dim

theorem exists_allocatedCanonicalProjection_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P coverLog : ℝ, 0 ≤ P → 0 ≤ coverLog →
      allocatedCanonicalProjectionLog m dim P coverLog ≤ (P + coverLog + A) ^ A := by
  obtain ⟨a, ha, hfourier⟩ := exists_allocatedFourierLogBudget_bound m
  let polynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
      Polynomial.C (canonicalProjectionRowCost m dim)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget polynomial
  refine ⟨A, hA, ?_⟩
  intro P coverLog hP hcoverLog
  have hpow : (P + a) ^ a ≤ (P + coverLog + a) ^ a := by
    gcongr
    linarith only [hcoverLog]
  have hpoly := hbound (P + coverLog) (add_nonneg hP hcoverLog)
  have hle : allocatedCanonicalProjectionLog m dim P coverLog ≤
      (P + coverLog + a) ^ a + (P + coverLog) + canonicalProjectionRowCost m dim := by
    unfold allocatedCanonicalProjectionLog
    linarith only [hfourier P hP, hpow, hP]
  apply hle.trans
  simpa [polynomial, Polynomial.eval₂_pow] using hpoly

theorem exists_allocatedCanonicalProjection_composed_budget (m dim Acover : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let coverLog := (P + (dim + 2 : ℕ) + Acover) ^ Acover
      let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
      coverLog ≤ (P + C) ^ C ∧
        (P + coverLog + Aproj) ^ Aproj ≤ (P + C) ^ C := by
  let Aproj := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
  let coverPolynomial : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (dim + 2) + Polynomial.C Acover) ^ Acover
  let densityPolynomial : Polynomial ℕ :=
    (Polynomial.X + coverPolynomial + Polynomial.C Aproj) ^ Aproj
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (coverPolynomial + densityPolynomial)
  refine ⟨C, hC, ?_⟩
  intro P hP coverLog Aprojection
  have hsum : coverLog + (P + coverLog + Aprojection) ^ Aprojection ≤ (P + C) ^ C := by
    simpa [coverPolynomial, densityPolynomial, Polynomial.eval₂_pow, coverLog,
      Aprojection, Aproj] using hbound P hP
  have hcover : 0 ≤ coverLog := by dsimp [coverLog]; positivity
  have hdensity : 0 ≤ (P + coverLog + Aprojection) ^ Aprojection := by positivity
  exact ⟨(le_add_of_nonneg_right hdensity).trans hsum,
    (le_add_of_nonneg_left hcover).trans hsum⟩

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.canonical_projection_bounds
    {P : ℝ} (h : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (dim : ℕ) {coverLog : ℝ} (hcoverLog : 0 ≤ coverLog) :
    let A := Classical.choose (exists_allocatedCanonicalProjection_budget m dim)
    let budget := (P + coverLog + A) ^ A
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let densityLip : ℝ≥0 := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip : ℝ≥0 := Fintype.card (Finset (Fin dim)) * Real.toNNReal (Real.exp coverLog)
    let reconstructionLip : ℝ≥0 :=
      ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) : ℝ≥0)
    cap ≤ Real.exp budget ∧
      ((densityLip * sectionLip * reconstructionLip : ℝ≥0) : ℝ) ≤ Real.exp budget := by
  intro A budget cap densityLip sectionLip reconstructionLip
  have hinput := allocatedCoefficient_fourier_input_budget (J := J) B R σ S.value S.positive C V
    h.nonneg h.degree h.variable_count hR hσ h.radius_inv h.width_inv h.coefficients
    h.real_axes h.integer_axes h.ambient_axes h.profile h.length h.chart h.covolume
  have hdensity : (densityLip : ℝ) ≤ Real.exp (allocatedFourierLogBudget m P) :=
    hinput.2.2.2
  have hpoly : allocatedCanonicalProjectionLog m dim P coverLog ≤ budget :=
    (Classical.choose_spec (exists_allocatedCanonicalProjection_budget m dim)).2 P coverLog
      h.nonneg hcoverLog
  have hfourier : allocatedFourierLogBudget m P ≤
      allocatedCanonicalProjectionLog m dim P coverLog := by
    unfold allocatedCanonicalProjectionLog
    exact (le_add_of_nonneg_right hcoverLog).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hrowCost : (canonicalProjectionRowCost m dim : ℝ) ≤
      Real.exp (canonicalProjectionRowCost m dim) := by
    linarith only [Real.add_one_le_exp (canonicalProjectionRowCost m dim : ℝ)]
  have hroweq : (sectionLip : ℝ) * reconstructionLip =
      Real.exp coverLog * (canonicalProjectionRowCost m dim : ℝ) := by
    simp only [sectionLip, reconstructionLip, canonicalProjectionRowCost,
      NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum, Real.coe_toNNReal,
      Real.exp_nonneg, Nat.cast_mul, Nat.cast_sum]
    ring
  refine ⟨hinput.2.2.1.trans (Real.exp_le_exp.mpr (hfourier.trans hpoly)), ?_⟩
  calc
    _ = (densityLip : ℝ) * ((sectionLip : ℝ) * reconstructionLip) := by
      simp only [NNReal.coe_mul, mul_assoc]
    _ = (densityLip : ℝ) * (Real.exp coverLog * (canonicalProjectionRowCost m dim : ℝ)) := by rw [hroweq]
    _ ≤ Real.exp (allocatedFourierLogBudget m P) *
        (Real.exp coverLog * Real.exp (canonicalProjectionRowCost m dim)) := by
      gcongr
    _ = Real.exp (allocatedCanonicalProjectionLog m dim P coverLog) := by
      simp only [allocatedCanonicalProjectionLog, Real.exp_add]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hpoly

end Erdos3.VectorPolynomial

end

end OAI
