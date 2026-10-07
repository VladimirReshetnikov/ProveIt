import OAI.Combinatorics.Progressions.Dynamics.AllocatedMixedSiteBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

local notation "degree" => Fin.val j + 1
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem exists_allocated_inactive_fixed_support_site_expansion
    [Nonempty (B ⟨j, Sum.inr i⟩)] {D P p v ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val (rowSets j).card (degree * (rowSets j).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let O := allocatedInactiveSiteOutputLog m D p v E
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rowSets j, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ (rowSets j).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ 2 * ε := by
  have hQ := (allocatedInactiveSiteBudgetLog_bounds m hD.nonneg hp hv hE).1
  obtain ⟨hHQ, hεQ, hLQ, hshortCap, hshortLip, herror⟩ :=
    allocatedInactiveSite_construction_bounds B rowSets hD hα hP hp hv hPp hε hε1 hE hεE q hqv ⟨j, i⟩
  obtain ⟨e, he, herr⟩ := exists_allocated_inactive_natural_site_expansion_all_cases
    B U b S j i q hq r hR hσ (rowSets j) P ε hsize hgamma hsmall hcell hgrid hσ1 A hA
    hprimitive hε hε1 hrows hB hε hQ hHQ hεQ hLQ hshortCap hshortLip herror
  obtain ⟨hT, hperiod, hC, hL⟩ := allocatedInactiveSite_output_bounds B rowSets hD hα hP hp hv hPp
    hε hε1 hE hεE ⟨j, i⟩
  refine ⟨e, he.mono hT hperiod hC ?_ (allocatedInactiveSiteRadius_exp_bound B rowSets hD ⟨j, i⟩), ?_⟩
  · exact_mod_cast hL
  · intro x y hy
    simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

local notation "degree" => Fin.val j + 1
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem exists_allocated_active_fixed_support_site_expansion
    {D P p ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hactive : S.value ^ degree < basisAxisScale (b j) i)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ S.value)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 2) * (rowSets j).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let O := allocatedActiveSiteOutputLog m D p E
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rowSets j, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ (rowSets j).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ 2 * ε := by
  let M : ℕ := torus * scale
  have htorus : 0 < torus := blockTorusFactor_pos _ _ _ _
  let : NeZero M := ⟨(Nat.mul_pos htorus (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)).ne'⟩
  let Q := allocatedActiveSiteBudgetLog m D p E
  obtain ⟨hQ, hcapQ, hspecQ, _⟩ := allocatedActiveSiteBudgetLog_bounds m hD.nonneg hp hE
  obtain ⟨hHQ, hεQ, hLQ⟩ := allocatedActiveSite_construction_bounds B rowSets hD hα hP hp hPp hε hE hεE ⟨j, i⟩
  obtain ⟨e, he, herr⟩ := exists_allocated_scalar_site_expansion (M := M) B U b hR hσ S q r j i
    hactive hq hsize (rowSets j) P ε hcell hgrid hgamma L hL hcP hsP rfl hrows hB hε hε1 hε hQ hHQ hεQ hLQ
  have hcard := allocatedNaturalGridSpectrum_cover_card (M := M) B U b hR S j i hactive hgrid hgamma hP
    (Nat.cast_nonneg torus) (by simp only [M, Nat.cast_mul]; exact le_rfl) (rowSets j) hε hε1
  have hs := allocatedActiveSpectrum_exp_bounds B rowSets hD hα hP hp hPp hε hE hεE ⟨j, i⟩
  have hspecQ' : allocatedActiveSpectrumLog m D p E ≤ Q := by
    have hnonneg := hD.nonneg
    linarith only [hspecQ, hnonneg]
  have hcardQ := hcard.trans (hs.1.trans (Real.exp_le_exp.mpr hspecQ'))
  have hperiodQ := hs.2.2.trans (Real.exp_le_exp.mpr hspecQ')
  have hcap := allocatedActivePointCap_exp_bound B rowSets hD hα hP hp hPp ⟨j, i⟩
  have hcapQ' : allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) ≤ Real.exp Q :=
    (le_trans (by linarith : allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) ≤
      allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) + 1) hcap).trans
      (Real.exp_le_exp.mpr (by linarith only [hcapQ, hE]))
  have hsites : Fintype.card (Finset α) ≤ 2 ^ (m + 1) := by
    rw [Fintype.card_finset]
    exact Nat.pow_le_pow_right (by norm_num) hα
  obtain ⟨hT, hperiod, hC, hLip, _⟩ := siteExponentialOutput_bounds
    (2 ^ (m + 1)) (Fintype.card (Finset α)) hsites hQ hcardQ hperiodQ hcapQ'
  have hfixed : allocatedNaturalSiteRadius (G := G) B j i (rowSets j) + 1 / 4 ≤
      Real.exp (allocatedInactiveSupportLog D) :=
    (allocatedNaturalSiteRadius_exp_bound B rowSets hD j i).trans (Real.exp_le_exp.mpr (by
      unfold allocatedNaturalSiteLog allocatedInactiveSupportLog
      linarith))
  refine ⟨e, he.mono hT hperiod hC ?_ hfixed, ?_⟩
  · exact_mod_cast hLip
  · intro x y hy
    simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

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
theorem exists_allocated_mixed_fixed_support_joint_site_expansion
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hselected : Function.Injective selected)
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hgamma : ∀ a, principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)) ≤ 1)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, max
      (positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
        ((layerTailDegree m + 2) * ((rows) a).card))
      (uniformSpectrumBlockCount (selected a).1.val ((rows) a).card
        (((selected a).1.val + 1) * ((rows) a).card)) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let O := allocatedMixedJointSiteLog m D p v E
    ∃ e : A → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
        (∀ a t, t ∉ (rows) a → booleanCoefficient (fun s => y s a) t = 0) →
        ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected (rows) x
            (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
          siteFamilyEval e y (fun s a => (y s a : ℝ) / (axisN) a)‖ ≤ δ := by
  let C := Real.exp (allocatedMixedPointCapLog m D p v)
  let τ := uniformProductAccuracy (Fintype.card A) C δ
  let O := allocatedMixedJointSiteLog m D p v E
  have hC : 0 ≤ C := (Real.exp_pos _).le
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) hC hδ
  have hε : 0 < τ / 2 := half_pos hτ
  have hε1 : τ / 2 ≤ 1 := by linarith only [hτ1]
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B rowSets hD)
  obtain ⟨hcapLog, hcapA, hcapI⟩ := allocatedMixedPointCapLog_bounds m hD.nonneg hp hv
  have hτinv := uniformProductAccuracy_inverse_exp_bound (Fintype.card A) hC hδ hD.nonneg hcapLog hE
    hcount (le_refl C) hδE
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hεinv : (τ / 2)⁻¹ ≤ Real.exp (allocatedMixedAccuracyLog m D p v E) := by
    rw [inv_div, div_eq_mul_inv]
    have hb := (mul_le_mul htwo hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hb.trans_eq (by unfold allocatedMixedAccuracyLog; congr 1; ring)
  have haccuracy := (allocatedMixedJointLogs_nonneg m hD.nonneg hp hv hE).1
  obtain ⟨_, houtA, houtI⟩ := allocatedMixedSiteOutputLog_bounds m hD.nonneg hp hv haccuracy
  have hAout : Real.exp (allocatedActiveSiteOutputLog m D p (allocatedMixedAccuracyLog m D p v E)) ≤
      Real.exp O := Real.exp_le_exp.mpr houtA
  have hIout : Real.exp (allocatedInactiveSiteOutputLog m D p v (allocatedMixedAccuracyLog m D p v E)) ≤
      Real.exp O := Real.exp_le_exp.mpr houtI
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hBa (a : A) : positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) :=
    (le_max_left _ _).trans (hB a)
  have hBi (a : A) : uniformSpectrumBlockCount (selected a).1.val ((rows) a).card
      (((selected a).1.val + 1) * ((rows) a).card) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) :=
    (le_max_right _ _).trans (hB a)
  have hnonempty (a : A) : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := by
    have hi := hBi a
    unfold uniformSpectrumBlockCount at hi
    exact Fintype.card_pos_iff.mp (by omega)
  have heach (a : A) : ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ (rows) a, booleanCoefficient y t = 0) →
        ‖((((axisN) a : ℝ) ^ ((rows) a).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (selected a).1 (selected a).2
            ((rows) a) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval ((axisN) a) y‖ ≤ 2 * (τ / 2) := by
    by_cases ha : S.value ^ ((selected a).1.val + 1) < basisAxisScale (b (selected a).1) (selected a).2
    · obtain ⟨e, he, herr⟩ := exists_allocated_active_fixed_support_site_expansion
        B U b S hR hσ rowSets (selected a).1 (selected a).2 q hq r hD hα hP hp hPp
        hε hε1 haccuracy hεinv ha hsize ((hgamma a).trans hS1) hcell (hgrid a) L hL hcP hsP
        (hrows a) (hBa a)
      exact ⟨e, he.mono hAout hAout hAout (by exact_mod_cast hAout) le_rfl, herr⟩
    · let : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := hnonempty a
      obtain ⟨e, he, herr⟩ := exists_allocated_inactive_fixed_support_site_expansion
        B U b S hR hσ rowSets (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv
        hε hε1 haccuracy hεinv hsize (hgamma a) (le_of_not_gt ha) hcell (hgrid a) (hσ1 a) L hL hsP
        (hrows a) (hBi a)
      exact ⟨e, he.mono hIout hIout hIout (by exact_mod_cast hIout) le_rfl, herr⟩
  choose e hb he using heach
  refine ⟨e, hb, ?_⟩
  apply allocatedJointGrid_site_approximation B U b hR hσ S q r hcell selected (rows)
    hselected hgrid (axisN) e hC hδ
  · intro a x z
    by_cases ha : S.value ^ ((selected a).1.val + 1) < basisAxisScale (b (selected a).1) (selected a).2
    · exact (allocatedActiveGrid_norm_exp_bound B U b S hR hσ rowSets
        (selected a).1 (selected a).2 q hq r hD hα hP hp hPp ha hsize ((hgamma a).trans hS1)
        hcell (hgrid a) L hL hcP hsP (hrows a) (hBa a) x z).trans (Real.exp_le_exp.mpr hcapA)
    · let : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := hnonempty a
      exact (allocatedInactiveGrid_norm_exp_bound B U b S hR hσ rowSets
        (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv hsize (hgamma a) (le_of_not_gt ha)
        hcell (hgrid a) L hL hsP (hrows a) (hBi a) x z).trans (Real.exp_le_exp.mpr hcapI)
  · intro a x y hy
    have herr := he a x y hy
    have hcancel : (2 : ℝ) * (τ / 2) = τ := by ring
    simpa only [hcancel] using herr

end Erdos3.VectorPolynomial

end

end OAI
