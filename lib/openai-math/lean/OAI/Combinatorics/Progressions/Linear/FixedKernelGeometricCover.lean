/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_retained_common_cover (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀] {q : ℕ}
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ (j : Fin m) s d, RationalHeightLE
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root₀ difference₀ s (some k)) s d : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P)
    (_hD : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent K₀ (j.val + 1)) : ℝ) ≤ P)
    (_hS : (Fintype.card (Finset (Fin q)) : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ) (e : K₀ → K)
    (_hroot : ∀ k, root (e k) = root₀ k) (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ i, Fintype (J i)]
    (U : ∀ i, Submodule ℝ (J i → ℝ)) (frequency : ∀ i, (K →₀ ℕ) → J i → ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hretained : affineCubeModeFactors U root difference frequency),
    ∃ b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ j s a, |(b j s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) (p : VectorPolynomial K ℝ (U j)), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter (U j) (b j)
          (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
            ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
              (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)) := by
  obtain ⟨A₀, _, hcover⟩ := exists_fixed_kernel_polynomial_cover
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget (C (m + 1) * (X + C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro K₀ _ q root₀ difference₀ a ha hperiod H hH hE P hP hD hS hHP
  choose D hDpos hDP hrows using fun j : Fin m =>
    hcover root₀ (Matrix.of difference₀) a ha hperiod (j.val + 1) hH (hE j) hP (hD j) hS hHP
  have hB : 0 ≤ (P + A₀) ^ A₀ := by positivity
  have hbud : ((m : ℝ) + 1) * (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hprod : (((∏ j, D j) : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * (P + A₀) ^ A₀) := by
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin m, Real.exp ((P + A₀) ^ A₀) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hDP j)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  refine ⟨∏ j, D j, Finset.prod_pos (fun j _ => hDpos j),
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith)), ?_⟩
  intro K _ root difference e hroot hdifference J _ U frequency C hC hCP hfrequency hretained
  choose M hM using fun j => affineCubeModeFactors_bounded U root difference frequency hretained j
  choose b hb hchar using fun j => hrows j root (Matrix.of difference) e hroot hdifference
    (U j) (frequency j) hC hCP (hfrequency j) (M j) (hM j)
  refine ⟨(fun j s a => (complementaryPeriod D j : ℤ) * b j s a), ?_, ?_⟩
  · intro j s a
    rw [Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ complementaryPeriod D j from Nat.cast_nonneg _)]
    calc
      _ ≤ (complementaryPeriod D j : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_left (hb j s a) (Nat.cast_nonneg _)
      _ ≤ (((∏ i, D i) : ℕ) : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (complementaryPeriod_le_product D hDpos j))
          (Real.exp_pos _).le
      _ ≤ Real.exp ((m : ℝ) * (P + A₀) ^ A₀) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = Real.exp (((m : ℝ) + 1) * (P + A₀) ^ A₀) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((P + A) ^ A) := Real.exp_le_exp.mpr hbud
  · intro j p hp
    exact (hchar j p hp).trans (subspaceArrayCharacter_common_period D hDpos j (U j) (b j)
      (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)).symm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem exists_fixed_kernel_geometric_cover (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ) (e : K₀ → K)
    (_hroot : ∀ k, root (e k) = root₀ k) (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ j d, d.degree ≤ j.val + 1 → ∀ a,
      |(frequency j d a : ℝ)| ≤ Real.exp P)
    (_hretained : affineCubeModeFactors U root difference frequency),
    ∃ b : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ j s a, |(b j s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) (p : VectorPolynomial K ℝ (U j)),
        DegreeLE (1 : K → ℕ) (j.val + 1) p →
        CircleFourier.character
          (coefficientFunctional (fun d a => (frequency j d a : ℝ))
            (map (U j).subtype p) : CircleFourier.Circle) =
        subspaceArrayCharacter (U j) (b j)
          (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
            ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
              (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p)) := by
  obtain ⟨A₀, _, hc⟩ := exists_fixed_kernel_retained_common_cover m
  obtain ⟨A, hA, hb⟩ := exists_geometricSiteBudget_absorption m q A₀
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  have hbudget := hb P hP
  have hPP := le_geometricSiteBudget m q hP
  obtain ⟨D, hD, hDP, hrows⟩ := hc root₀ difference₀ a ha hperiod
    (exponentialSiteHeight_pos m P)
    (fun j s d => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt)
      (fun s k => affineSite root₀ difference₀ s (some k)) hsite s d)
    (geometricSiteBudget_nonneg m q hP)
    (fun j => boundedCoefficientExponent_card_le_geometricSiteBudget m q
      (Nat.succ_le_of_lt j.isLt) hP hK)
    (cubeSites_card_le_geometricSiteBudget m q hP)
    ((exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hbudget), ?_⟩
  intro K _ root difference e hroot hdifference J _ U frequency hfrequency hretained
  obtain ⟨b, hbnd, hchar⟩ := hrows root difference e hroot hdifference U frequency (Real.exp_pos P).le
    (Real.exp_le_exp.mpr hPP) hfrequency hretained
  exact ⟨b, fun j s a => (hbnd j s a).trans (Real.exp_le_exp.mpr hbudget), hchar⟩

end Erdos3.BooleanCubeKernel

end

end OAI
