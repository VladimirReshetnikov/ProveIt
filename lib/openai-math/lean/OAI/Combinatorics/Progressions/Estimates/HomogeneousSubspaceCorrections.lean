import OAI.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
import OAI.Combinatorics.Progressions.Lattices.DerivativeLatticeDivision
import OAI.Combinatorics.Progressions.Polynomial.ControlledSubspaceCorrectionPolynomials

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

theorem reconstructDerivatives_coordinate_bound {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] ℝ) (P : σ → VectorPolynomial σ ℚ V)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ i α, |f (coefficients (P i) α)| ≤ M / (T i * monomialScale T α))
    (β : σ →₀ ℕ) :
    |f (coefficients (reconstructDerivatives d P) β)| ≤
      ((Fintype.card σ : ℝ) / d * M) / monomialScale T β := by
  classical
  have hscale (i : σ) (hi : i ∈ β.support) :
      T i * monomialScale T (β - Finsupp.single i 1) = monomialScale T β := by
    calc
      _ = monomialScale T ((β - Finsupp.single i 1) + Finsupp.single i 1) := by
        rw [monomialScale_add]
        simp [monomialScale, mul_comm]
      _ = _ := by rw [Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)]
  have hc : f (coefficients (reconstructDerivatives d P) β) =
      (d : ℝ)⁻¹ * ∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0 := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
  have hsum : |∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| ≤
      (Fintype.card σ : ℝ) * (M / monomialScale T β) := by
    calc
      _ ≤ ∑ i, |if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : σ, M / monomialScale T β := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact (hP i (β - Finsupp.single i 1)).trans_eq
            (congrArg (fun q : ℝ => M / q) (hscale i hi))
        · rw [abs_zero]
          exact div_nonneg hM (monomialScale_pos T hT β).le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hc, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)]
  calc
    _ ≤ (d : ℝ)⁻¹ * ((Fintype.card σ : ℝ) * (M / monomialScale T β)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)
    _ = _ := by ring

theorem reconstructDerivatives_coordinate_grid {ι : Type*} {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] (ι → ℝ)) (P : σ → VectorPolynomial σ ℚ V) (l : ℕ)
    (hP : ∀ i α, f (coefficients (P i) α) ∈ realDenominatorGrid l) (β : σ →₀ ℕ) :
    f (coefficients (reconstructDerivatives d P) β) ∈ realDenominatorGrid (l * d) := by
  classical
  let v : σ → ι → ℝ := fun i =>
    if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0
  have hv (i : σ) : v i ∈ realDenominatorGrid l := by
    dsimp [v]
    split_ifs
    · exact hP i _
    · exact ⟨0, by ext j; simp⟩
  have hsum : (∑ i, v i) ∈ realDenominatorGrid l := by
    have h := realDenominatorGrid_linear_combination 1 l (fun _ : σ => (1 : ℝ)) v
      (by exact ⟨fun _ => 1, by ext i; simp⟩) hv
    simpa only [one_smul, Nat.mul_one] using h
  have hc : f (coefficients (reconstructDerivatives d P) β) = (d : ℝ)⁻¹ • ∑ i, v i := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero]
    change (d : ℚ)⁻¹ • (∑ i, v i) = (d : ℝ)⁻¹ • ∑ i, v i
    ext j
    simp [Pi.smul_apply, Rat.smul_def]
  rw [hc]
  exact realDenominatorGrid_div_nat l d hd _ hsum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ V ι : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

theorem exists_homogeneous_split_from_derivatives (W : Submodule ℚ V)
    {d : ℕ} (hd : 0 < d) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0)
    (S R : σ → VectorPolynomial σ ℚ V)
    (hS : ∀ i β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d - 1 → coefficients (S i) β = 0)
    (hR : ∀ i β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d - 1 → coefficients (R i) β = 0)
    (hsplit : ∀ i β, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor V P - S i - R i) β ∈ W)
    (coord : V →ₗ[ℚ] (ι → ℝ)) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (l : ℕ)
    (hslow : ∀ i β n, |coord (coefficients (S i) β) n| ≤ M / (T i * monomialScale T β))
    (hrational : ∀ i β, coord (coefficients (R i) β) ∈ realDenominatorGrid l) :
    ∃ A B : VectorPolynomial σ ℚ V,
      (∀ β, coefficients (P - A - B) β ∈ W) ∧
      (∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients A β = 0) ∧
      (∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients B β = 0) ∧
      (∀ β n, |coord (coefficients A β) n| ≤
        ((Fintype.card σ : ℝ) / d * M) / monomialScale T β) ∧
      ∀ β, coord (coefficients B β) ∈ realDenominatorGrid (l * d) := by
  refine ⟨reconstructDerivatives d S, reconstructDerivatives d R,
    homogeneous_derivative_split_mod W hd P hP S R hsplit,
    reconstructDerivatives_homogeneous hd S hS,
    reconstructDerivatives_homogeneous hd R hR, ?_, ?_⟩
  · intro β n
    exact reconstructDerivatives_coordinate_bound hd ((LinearMap.proj n).comp coord)
      S T hT hM (fun i α => hslow i α n) β
  · intro β
    exact reconstructDerivatives_coordinate_grid hd coord R l hrational β

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {E V : Submodule ℚ L}

theorem exists_homogeneous_subspace_corrections_from_derivatives
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l d : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hd : 0 < d)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * d : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients P α = 0)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / d * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d S) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) (reconstructDerivatives d R) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  have hShom := reconstructDerivatives_homogeneous hd S hS
  have hRhom := reconstructDerivatives_homogeneous hd R hR
  have hS0 : coefficients (reconstructDerivatives d S) 0 = 0 :=
    hShom 0 (by simpa using Nat.ne_of_lt hd)
  have hR0 : coefficients (reconstructDerivatives d R) 0 = 0 :=
    hRhom 0 (by simpa using Nat.ne_of_lt hd)
  have hSnorm (α : σ →₀ ℕ) :
      ‖realQuotientCoordinateMap f (coefficients (reconstructDerivatives d S) α)‖ ≤
        Real.exp p / monomialScale T α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
      (monomialScale_pos T hTpos α).le)).mpr
    intro n
    rw [Real.norm_eq_abs]
    have hbound := reconstructDerivatives_coordinate_bound hd ((LinearMap.proj n).comp q)
      S T hTpos hM (fun i β => hslow i β n) α
    exact hbound.trans (div_le_div_of_nonneg_right hbudget (monomialScale_pos T hTpos α).le)
  have hRgrid (α : σ →₀ ℕ) :
      realQuotientCoordinateMap f (coefficients (reconstructDerivatives d R) α) ∈
        realDenominatorGrid (l * d) :=
    reconstructDerivatives_coordinate_grid hd q R l hrational α
  have hres := homogeneous_derivative_split_mod ((V.baseChange ℝ).restrictScalars ℚ)
    hd P hP S R hsplit
  have h := exists_controlled_subspace_correction_polynomials b e f hH (Nat.mul_pos hl hd)
    hA he hp hrows hcols hHp hlp T hT P (reconstructDerivatives d S)
    (reconstructDerivatives d R) hPE hS0 hR0 hSnorm hRgrid hres
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hE, hAz, hBz, hAnorm, hBgrid, hresidual⟩ := h
  exact ⟨m, A, B, hm, hmp, hAQ, hBQ, hE,
    fun α hα => hAz α (hShom α hα), fun α hα => hBz α (hRhom α hα),
    hAnorm, hBgrid, hresidual⟩

end Erdos3

end

end OAI
