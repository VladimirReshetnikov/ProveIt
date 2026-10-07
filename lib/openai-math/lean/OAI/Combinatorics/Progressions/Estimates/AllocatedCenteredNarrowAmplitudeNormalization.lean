import OAI.Combinatorics.Progressions.Fourier.AllocatedPositiveFourierData
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeDensityTest
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
import OAI.Combinatorics.Progressions.Probability.SelectedDensityTestMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_amplitude_density_test m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hlocal (base : X → ℤ)
      (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ)
      (hamp : ∀ x, ‖amplitude x‖ ≤ 1) {Lip : ℝ≥0}
      (hLip : LipschitzWith Lip amplitude) (hLipP : (Lip : ℝ) ≤ Real.exp P) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    obtain ⟨hZ, hclose⟩ := hmass hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      (Real.exp_nonneg Q) le_rfl frequency
      (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank) T hT widths hwidths
      hwidthLower amplitude hamp hLip (hLipP.trans hExp)
      (allocatedCoefficientDensity B U basis hb o hR hσ S) hspec.2.2.1 hspec.2.2.2.1 hη.le happ
    refine ⟨hZ, ?_⟩
    exact hclose.trans_eq (by ring)
  obtain ⟨hZ, _⟩ := hlocal 0 (fun _ => 0) (by simp) (LipschitzWith.const 0)
    (by simpa using (Real.exp_nonneg P))
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro base amplitude hamp Lip hLip hLipP
    exact (hlocal base amplitude hamp hLip hLipP).choose_spec
  · intro base
    have hmass := selectedResidueDensityMass_bound_of_constant_test stride T widths hwidths hZ
      (density base) ((hlocal base (fun _ => 1) (by simp) (LipschitzWith.const 1)
        (by simpa using (Real.exp_nonneg P))).choose_spec)
    have hD0 : ∀ z, 0 ≤ density base z := fun _ => hspec.2.1 _
    have hD := (positiveProjectionAccuracy_normalizer hP hmass).2.2.1
    refine ⟨hmass, hD0, hD, ?_⟩
    intro amplitude hamp Lip hLip hLipP
    have htest := (hlocal base amplitude hamp hLip hLipP).choose_spec
    have hn := selectedResidueDensityPMF_error_of_bounded_test stride T widths hwidths hZ
      (density base) hD0 hD (fun z => amplitude (fun t => (z t : ℝ) / widths t))
      (fun z => hamp _) htest hmass
    exact hn.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ center base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A, hA, hnormalization⟩ := exists_allocated_narrow_amplitude_normalization m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths density
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    have hp' (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (subtractConstant (c j).val (p j)) :=
      (hp j).subtractConstant _
    have hm' := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
    have hrank' (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j)
        (subtractConstant (c j).val (p j)) :=
      (hasLayerSamplingRank_subtractConstant_iff (by omega) _ _ _ _ _).mpr (hrank j)
    have h := hnormalization B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv
      hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
      (fun j => subtractConstant (c j).val (p j)) hp' hm' stride hs hsP hW hWP hτ hτP hξ hξ1 hξP
      N hsize hrank' hRank T hT
    have heq := allocatedJointBaseDensity_subtractConstant_centered B U basis hb o hR hσ S p hm
      center c hc
    obtain ⟨hw, hZ, hraw, hnorm⟩ := h
    refine ⟨hw, hZ, ?_, ?_⟩
    · intro base amplitude hamp Lip hLip hLipP
      have hh := hraw base amplitude hamp hLip hLipP
      simpa only [density, ← heq, allocatedJointBaseDensity] using hh
    · intro base
      obtain ⟨hmass, _, _, _⟩ := hnorm base
      have hmass' : |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P := by
        dsimp only [density]
        rw [← heq]
        unfold allocatedJointBaseDensity
        exact hmass
      have hD0' : ∀ z, 0 ≤ density center base z := fun z =>
        allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center base z
      have hD' := (positiveProjectionAccuracy_normalizer hP hmass').2.2.1
      refine ⟨hmass', hD0', hD', ?_⟩
      intro amplitude hamp Lip hLip hLipP
      have hh := selectedResidueDensityPMF_error_of_bounded_test stride T widths hw hZ
        (density center base) hD0' hD'
        (fun z => amplitude (fun t => (z t : ℝ) / widths t)) (fun _ => hamp _)
        (ε := 3 * positiveProjectionAccuracy P)
        (by simpa only [density, ← heq, allocatedJointBaseDensity] using
          hraw base amplitude hamp hLip hLipP) hmass'
      exact hh.trans_eq (by ring)
  obtain ⟨hwidths, hZ, _, _⟩ := hcenter 0
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro center base amplitude hamp Lip hLip hLipP
    obtain ⟨_, _, hraw, _⟩ := hcenter center
    exact hraw base amplitude hamp hLip hLipP
  · intro center base
    obtain ⟨_, _, _, hnorm⟩ := hcenter center
    exact hnorm base

end Erdos3.VectorPolynomial

end

end OAI
