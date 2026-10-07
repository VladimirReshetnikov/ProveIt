import OAI.Combinatorics.Progressions.Lattices.AffineCoveredJetDensity

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem exists_fixed_kernel_site_residual (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
    ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
      (x : BoundedCoefficientExponent K (j.val + 1) → W),
      let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
      matrixModuleAction (fun s i => (E s i : ℝ))
        (matrixModuleAction (fun i s => (T j i s : ℝ))
          (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
        (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  classical
  obtain ⟨A, hA, hbudget⟩ := exists_geometric_positive_cover_budget m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  let site₀ := fun s k => affineSite root₀ difference₀ s (some k)
  let E₀ := fun j : Fin m => boundedSiteMatrix (j.val + 1) site₀
  obtain ⟨d, T₀, hd, hT₀, hbound⟩ := exists_common_integer_site_residual E₀
    (fun _ => exponentialSiteHeight m P) (fun _ => exponentialSiteHeight_pos m P)
    (fun j => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt) site₀ hsite)
  have hdb := hbound (geometricSiteBudget_nonneg m q hP)
    (fun j => boundedCoefficientExponent_card_le_geometricSiteBudget m q
      (Nat.succ_le_of_lt j.isLt) hP hK)
    (cubeSites_card_le_geometricSiteBudget m q hP)
    (fun _ => (exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr (by
    simpa only [Fintype.card_fin] using hbudget P hP)), ?_⟩
  intro K _ root difference e hroot hdifference
  let site := fun s k => affineSite root difference s (some k)
  have hs : (fun s k => site s (e k)) = site₀ := by
    funext s k
    simp only [site, site₀, affineSite, hroot, hdifference]
  refine ⟨fun j => extendIntegerSiteSection (boundedExponentMap e (j.val + 1)) (T₀ j), ?_⟩
  intro j W _ _ x
  have hc : (boundedSiteMatrix (j.val + 1) site).submatrix id (boundedExponentMap e (j.val + 1)) = E₀ j := by
    rw [boundedSiteMatrix_mapDomain, hs]
  obtain ⟨R, hR⟩ := boundedSiteMatrix_fixed_kernel_factor root₀ (Matrix.of difference₀)
    a ha hperiod (j.val + 1) root (Matrix.of difference)
  exact integerSiteResidual_extend_columns (E₀ j) (boundedSiteMatrix (j.val + 1) site)
    (boundedExponentMap e (j.val + 1)) hc R hR (T₀ j) d (hT₀ j) x

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

theorem exists_bounded_residual_cover_budget (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      geometricSiteBudget m q P + ((m : ℝ) + 2) * (geometricSiteBudget m q P + 2) ^ 36 ≤
        (P + A) ^ A := by
  let G : Polynomial ℕ := C (m + 1) * (X + 1) ^ (m + 1) + C (2 ^ q)
  obtain ⟨A, hA, h⟩ := exists_natPolynomial_eval_budget (G + C (m + 2) * (G + 2) ^ 36)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [G, geometricSiteBudget, Polynomial.eval₂_pow, Nat.cast_add] using h P hP

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A, hA, hbudget⟩ := exists_bounded_residual_cover_budget m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  let site₀ := fun s k => affineSite root₀ difference₀ s (some k)
  let E₀ := fun j : Fin m => boundedSiteMatrix (j.val + 1) site₀
  obtain ⟨d, T₀, hd, hT₀, hbound⟩ := exists_bounded_common_site_residual E₀
    (fun _ => exponentialSiteHeight m P) (fun _ => exponentialSiteHeight_pos m P)
    (fun j => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt) site₀ hsite)
  let G := geometricSiteBudget m q P
  have hG : 0 ≤ G := geometricSiteBudget_nonneg m q hP
  have hcard (j : Fin m) : (Fintype.card (BoundedCoefficientExponent K₀ (j.val + 1)) : ℝ) ≤ G :=
    boundedCoefficientExponent_card_le_geometricSiteBudget m q (Nat.succ_le_of_lt j.isLt) hP hK
  obtain ⟨hdb, hTb⟩ := hbound hG hcard (cubeSites_card_le_geometricSiteBudget m q hP)
    (fun _ => (exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  have hcost : G + ((m : ℝ) + 2) * (G + 2) ^ 36 ≤ (P + A) ^ A := hbudget P hP
  have hpow : 0 ≤ (G + 2) ^ 36 := pow_nonneg (by linarith) _
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr ?_), ?_⟩
  · simp only [Fintype.card_fin]
    nlinarith
  · intro K _ root difference e hroot hdifference
    let site := fun s k => affineSite root difference s (some k)
    have hs : (fun s k => site s (e k)) = site₀ := by
      funext s k
      simp only [site, site₀, affineSite, hroot, hdifference]
    refine ⟨fun j => extendIntegerSiteSection (boundedExponentMap e (j.val + 1)) (T₀ j), ?_, ?_⟩
    · intro j s
      apply (extendIntegerSiteSection_column_sum_bound _ (T₀ j) (hTb j) s).trans
      simp only [Fintype.card_fin]
      calc
        _ ≤ G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (hcard j) (Real.exp_pos _).le
        _ ≤ Real.exp G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp G]) (Real.exp_pos _).le
        _ = Real.exp (G + ((m : ℝ) + 2) * (G + 2) ^ 36) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hcost
    · intro j W _ _ x
      have hc : (boundedSiteMatrix (j.val + 1) site).submatrix id (boundedExponentMap e (j.val + 1)) = E₀ j := by
        rw [boundedSiteMatrix_mapDomain, hs]
      obtain ⟨R, hR⟩ := boundedSiteMatrix_fixed_kernel_factor root₀ (Matrix.of difference₀)
        a ha hperiod (j.val + 1) root (Matrix.of difference)
      exact integerSiteResidual_extend_columns (E₀ j) (boundedSiteMatrix (j.val + 1) site)
        (boundedExponentMap e (j.val + 1)) hc R hR (T₀ j) d (hT₀ j) x

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A₀, _, hsection⟩ := exists_fixed_kernel_bounded_section m q
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C A₀) ^ A₀)
  have hbudget (P : ℝ) (hP : 0 ≤ P) : P + (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite
  have hbound {x : ℝ} (hx : x ≤ Real.exp ((P + A₀) ^ A₀)) :
      period * x ≤ Real.exp ((P + A) ^ A) := by
    calc
      _ ≤ (period : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right hpP (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (hbudget P hP)
  refine ⟨period * d, dvd_mul_right period d, Nat.mul_pos hp hd, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hbound hdb
  · intro K _ root difference e hroot hdifference
    obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
    refine ⟨fun j i s => (period : ℤ) * T j i s, ?_, ?_⟩
    · intro j s
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg period : (0 : ℝ) ≤ period), ← Finset.mul_sum]
      exact hbound (hTb j s)
    · intro j W _ _ x
      dsimp only
      rw [matrixModuleAction_int_smul, map_smul, hT j x, smul_smul, Nat.cast_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_covered_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
      (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
      (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let E := coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
      let π := Set.rangeFactorization E
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      ∃ g : Set.range E → ℝ, Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) B) ∧
        Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map π = realDensityMeasure (μ.map π) g ∧
        ∀ {I F : Type*} [Fintype F]
          (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (b : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c b -
              (g (π (affineCoefficientCoverSample U p hm d b)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hresidual⟩ := exists_fixed_kernel_site_residual m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hextend⟩ := hresidual root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference
  obtain ⟨T, hT⟩ := hextend root difference e hroot hdifference
  let site := fun s k => affineSite root difference s (some k)
  intro J _ U _ _ _ _ _ μ _ _ D hD B hcap hmass E π C
  let R := coefficientSiteResidual U site (fun _ => d) T
  let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
  obtain ⟨g, hgc, hgb, hgi, hgmass, hg, hlaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ D hD hcap hmass
  refine ⟨g, hgc, hgb, hgi, hgmass, hlaw, ?_⟩
  intro I F _ frequency c η happrox p hp hm b
  have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
      (coefficientArrayFunctional U frequency).comp R = 0 ↔
        affineCubeModeFactors U root difference frequency := by
    change (coefficientArrayFunctional U frequency).comp
      (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
    rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
      affineCubeModeFactors_iff_bounded]
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
    frequency c μ D happrox (affineSampleCoefficientTorus U p hm b)
    (coefficientResidual_section_integrable U R hR μ D hD hb _)
  have hvalue := hg (affineCoefficientCoverSample U p hm d b)
  rw [affineCoefficientCoverSample_projection U p hm d hd b] at hvalue
  rw [hvalue]
  simpa only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

theorem exists_fixed_kernel_euclidean_density (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
      ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
      (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
      (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      [CompactSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
      [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
      (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (D : CoefficientTorus (K := K) U → ℝ), Continuous D →
      ∀ {B : ℝ}, (∀ x, D x ∈ Set.Icc (0 : ℝ) B) → (∫ x, D x ∂μ) = 1 →
      let F := euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      let C := quotientIntegerCover (coefficientIntegerLattice U) d
      let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
      ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
        Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) B) ∧ Integrable f ξ ∧
        (∫ z, f z ∂ξ) = 1 ∧
        (realDensityMeasure μ (fun x => D (C x))).map F = realDensityMeasure ξ f ∧
        ∀ {I G : Type*} [Fintype G]
          (frequency : G → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : G → ℂ) {η : ℝ},
          (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
          ∀ (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (b : Option K → I → ℝ),
            ‖affineCubeFourierProjection U root difference frequency p c b -
              (f (F (affineCoefficientCoverSample U p hm d b)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_covered_density m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨d, hd, hdb, hcover⟩ := hcover root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨d, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ D hD B hcap hmass F C ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, hgc, hgb, _, hgmass, hglaw, hgapprox⟩ :=
    hcover root difference e hroot hdifference U μ D hD hcap hmass
  obtain ⟨hfc, hfb, hfi, hfmass, hvalue, hflaw⟩ := siteImage_density_euclideanJet U root
    (Matrix.of difference) a ha hfull μ ν (realDensityMeasure μ (fun x => D (C x)))
    g hgc hgb hgmass hglaw
  refine ⟨_, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro I G _ frequency c η happrox p hp hm b
  have he := hvalue (Set.rangeFactorization
    (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
    (affineCoefficientCoverSample U p hm d b))
  change (g ((euclideanSiteImageHomeomorph U root (Matrix.of difference) a ha hfull).symm
    (F (affineCoefficientCoverSample U p hm d b)))) = _ at he
  rw [he]
  exact hgapprox frequency c happrox p hp hm b

end Erdos3.BooleanCubeKernel

end

end OAI
