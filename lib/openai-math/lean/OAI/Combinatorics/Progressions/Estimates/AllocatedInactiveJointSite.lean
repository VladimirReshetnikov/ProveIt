import OAI.Combinatorics.Progressions.Dynamics.AllocatedActiveBudgetedSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

def allocatedInactiveJointAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D p v E : A) : A :=
  uniformProductAccuracyLog D (allocatedInactivePointCapLog m D p v) E + 1

def allocatedInactiveJointSiteLog {A : Type*} [Semiring A]
    (m : ℕ) (D p v E : A) : A :=
  allocatedInactiveSiteOutputLog m D p v (allocatedInactiveJointAccuracyLog m D p v E)

noncomputable def allocatedInactiveJointPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p v E : A) : A :=
  allocatedInactiveJointSiteLog m (allocatedComparisonDimension m p) p v E

theorem allocatedInactiveJointLogs_nonneg (m : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedInactiveJointAccuracyLog m D p v E ∧ 0 ≤ allocatedInactiveJointSiteLog m D p v E := by
  have hT := allocatedInactivePointCapLog_nonneg m hD hp hv
  have hU := uniformProductAccuracyLog_nonneg hD hT hE
  have hA : 0 ≤ allocatedInactiveJointAccuracyLog m D p v E := by
    unfold allocatedInactiveJointAccuracyLog
    positivity
  exact ⟨hA, (allocatedInactiveSiteOutputLog_bounds m hD hp hv hA).1⟩

theorem exists_allocatedInactiveJointPrimitiveLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedInactiveJointPrimitiveLog m p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedInactiveJointPrimitiveLog m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedInactiveJointPrimitiveLog, allocatedInactiveJointSiteLog,
    allocatedInactiveJointAccuracyLog, uniformProductAccuracyLog, allocatedInactivePointCapLog,
    inactiveShortCapLog, allocatedInactiveSiteOutputLog, allocatedInactiveSiteBudgetLog,
    inactiveShortLipschitzLog, inactiveShortScaleLog, allocatedInactiveSupportLog,
    allocatedInactiveSpectrumLog, allocatedComparisonDimension, allocatedInactiveTorusLog,
    allocatedInactiveScaleLog, uniformRetainedComplexityLog, uniformSpectrumSizeLog,
    uniformSpectrumCardLog, uniformRetainedFrequencyLog, uniformRetainedDenominatorLog,
    uniformRetainedBiasLog, uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog,
    majorArcLengthLog, majorArcBiasLog, majorArcErrorLog, majorArcLocalizationLog,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))

local notation "rows" => fun a : A => rowSets (Sigma.fst (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

include hq in
theorem exists_allocated_inactive_joint_site_expansion
    [∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)]
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hselected : Function.Injective selected)
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hgamma : ∀ a, principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)) ≤ 1)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤ S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val ((rows) a).card
      (((selected a).1.val + 1) * ((rows) a).card) ≤
        Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let O := allocatedInactiveJointSiteLog m D p v E
    ∃ e : A → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp O)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
        (∀ a t, t ∉ (rows) a → booleanCoefficient (fun s => y s a) t = 0) →
        ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected (rows) x
            (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
          siteFamilyEval e y (fun s a => (y s a : ℝ) / (axisN) a)‖ ≤ δ := by
  let C := Real.exp (allocatedInactivePointCapLog m D p v)
  let τ := uniformProductAccuracy (Fintype.card A) C δ
  have hC : 0 ≤ C := (Real.exp_pos _).le
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) hC hδ
  have hε : 0 < τ / 2 := half_pos hτ
  have hε1 : τ / 2 ≤ 1 := by linarith only [hτ1]
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B rowSets hD)
  have hcapLog := allocatedInactivePointCapLog_nonneg m hD.nonneg hp hv
  have hτinv := uniformProductAccuracy_inverse_exp_bound (Fintype.card A) hC hδ hD.nonneg hcapLog hE
    hcount (le_refl C) hδE
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hεinv : (τ / 2)⁻¹ ≤ Real.exp (allocatedInactiveJointAccuracyLog m D p v E) := by
    rw [inv_div, div_eq_mul_inv]
    have hb := (mul_le_mul htwo hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hb.trans_eq (by unfold allocatedInactiveJointAccuracyLog; congr 1; ring)
  have haccuracy := (allocatedInactiveJointLogs_nonneg m hD.nonneg hp hv hE).1
  have heach (a : A) := exists_allocated_inactive_budgeted_site_expansion
    B U b S hR hσ rowSets (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv
    hε hε1 haccuracy hεinv hsize (hgamma a) (hsmall a) hcell (hgrid a) (hσ1 a) L hL
    hprimitive (hrows a) (hB a)
  choose e hb he using heach
  refine ⟨e, hb, ?_⟩
  apply allocatedJointGrid_site_approximation B U b hR hσ S q r hcell selected (rows)
    hselected hgrid (axisN) e hC hδ
  · intro a x z
    exact allocatedInactiveGrid_norm_exp_bound B U b S hR hσ rowSets
      (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv hsize
      (hgamma a) (hsmall a) hcell (hgrid a) L hL hprimitive (hrows a) (hB a) x z
  · intro a x y hy
    have herr := he a x y hy
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using herr

end Erdos3.VectorPolynomial

end

end OAI
