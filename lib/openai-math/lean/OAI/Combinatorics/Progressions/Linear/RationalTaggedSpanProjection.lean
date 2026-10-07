import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
import OAI.Combinatorics.Progressions.Linear.RealRationalMatrixPiNaturality

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem rationalMatrix_real_ker_eq_range
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      LinearMap.range (Matrix.mulVecLin (fun i k => (A i k : ℝ))) := by
  classical
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hex : Function.Exact (A.mulVecLin.baseChange ℝ) (D.mulVecLin.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ (LinearMap.exact_iff.mpr h)
  ext x
  change Matrix.mulVecLin (fun j i => (D j i : ℝ)) x = 0 ↔
    ∃ y, Matrix.mulVecLin (fun i k => (A i k : ℝ)) y = x
  constructor
  · intro hx
    have hx' : D.mulVecLin.baseChange ℝ
        ((TensorProduct.piScalarRight ℚ ℝ ℝ I).symm x) = 0 := by
      apply (TensorProduct.piScalarRight ℚ ℝ ℝ J).injective
      rw [rationalMatrix_piScalarRight_baseChange, map_zero,
        LinearEquiv.apply_symm_apply]
      exact hx
    obtain ⟨z, hz⟩ := (hex _).mp hx'
    refine ⟨TensorProduct.piScalarRight ℚ ℝ ℝ K z, ?_⟩
    rw [← rationalMatrix_piScalarRight_baseChange, hz,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    have hz := hex.apply_apply_eq_zero
      ((TensorProduct.piScalarRight ℚ ℝ ℝ K).symm y)
    have he := congrArg (TensorProduct.piScalarRight ℚ ℝ ℝ J) hz
    simpa only [rationalMatrix_piScalarRight_baseChange,
      LinearEquiv.apply_symm_apply, map_zero] using he

theorem rationalMatrix_real_ker_eq_span
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      Submodule.span ℝ (Set.range (fun k i => (A i k : ℝ))) := by
  rw [rationalMatrix_real_ker_eq_range A D h]
  exact Matrix.range_mulVecLin (fun i k => (A i k : ℝ) : Matrix I K ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem matrixDenominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (matrixDenominator D : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hcard : (Fintype.card (ι × κ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hι.trans (by linarith)) (hκ.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  simpa only [matrixDenominator, arrayDenominator, Nat.cast_prod] using
    product_exponential_budget Finset.univ (fun ij : ι × κ => ((D ij.1 ij.2).den : ℝ))
      hp a 2 (fun _ _ => Nat.cast_nonneg _) (fun ij _ => hD ij.1 ij.2) hcard

theorem matrix_weighted_factor_le_exp_power (n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a) :
    ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ a) + 1) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hA : 1 ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
  have hpA : p ≤ (p + 2) ^ a := le_power_budget hp ha
  have hplus : Real.exp ((p + 2) ^ a) + 1 ≤ Real.exp ((p + 2) ^ a + 1) := by
    calc
      _ ≤ Real.exp ((p + 2) ^ a) * 2 := by
        have h := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ (p + 2) ^ a)
        linarith
      _ ≤ Real.exp ((p + 2) ^ a) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a + 1) :=
      mul_le_mul (by linarith [Real.add_one_le_exp p]) hplus (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + ((p + 2) ^ a + 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * (p + 2) ^ a := by linarith
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ a :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [pow_add]; ring

theorem matrix_pair_denominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hS : ∀ i j, ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator D * matrixDenominator S * l : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (a + 4)) := by
  have hDb := matrixDenominator_le_exp_power D hp a hκ hι hD
  have hSb := matrixDenominator_le_exp_power S hp a hι hκ hS
  have hlb := hl.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega : 1 ≤ a + 2)))
  rw [Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp ((p + 2) ^ (a + 2)) * Real.exp ((p + 2) ^ (a + 2)) *
        Real.exp ((p + 2) ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hDb hSb (Nat.cast_nonneg _) (Real.exp_nonneg _)) hlb
        (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (3 * (p + 2) ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + 2) ^ (a + 4)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 2) ^ 2 * (p + 2) ^ (a + 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem rationalKernelSeparationConstant_ceil_le_exp_power
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℚ) {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp ((p+2)^a))
    (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    (⌈(matrixDenominator Q : ℝ) *
      (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))⌉₊ : ℝ) ≤
        Real.exp ((p+2)^(a+4)) := by
  let c : ℝ := (matrixDenominator Q : ℝ) *
    (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))
  have hden := matrixDenominator_le_exp_power Q hp a hι hκ
    (fun i j => (Nat.cast_le.mpr (hQ i j).2).trans hH)
  have hfactor : ((Fintype.card κ : ℝ)+1)*((H : ℝ)+1) ≤
      Real.exp ((p+2)^(a+2)) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ a ha)
    exact mul_le_mul_of_nonneg_left (by linarith only [hH]) (by positivity)
  have hc : c ≤ Real.exp ((p+2)^(a+3)) := by
    calc
      _ ≤ Real.exp ((p+2)^(a+2)) * Real.exp ((p+2)^(a+2)) :=
        mul_le_mul hden hfactor (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2*(p+2)^(a+2)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p+2)*(p+2)^(a+2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by rw [pow_succ]; ring
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hceil : (⌈c⌉₊ : ℝ) ≤ c+1 := (Nat.ceil_lt_add_one hc0).le
  change (⌈c⌉₊ : ℝ) ≤ _
  calc
    _ ≤ Real.exp ((p+2)^(a+3))+1 := hceil.trans (by linarith only [hc])
    _ ≤ Real.exp ((p+2)^(a+3)) * 2 := by
      have hExp := Real.one_le_exp_iff.mpr (show 0 ≤ (p+2)^(a+3) by positivity)
      linarith only [hExp]
    _ ≤ Real.exp ((p+2)^(a+3)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp ((p+2)^(a+3)+1) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hbase : 1 ≤ (p+2)^(a+3) := one_le_pow₀ (by linarith)
      calc
        _ ≤ 2*(p+2)^(a+3) := by linarith only [hbase]
        _ ≤ (p+2)*(p+2)^(a+3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix BigOperators

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (e : Basis κ ℚ V)

omit [Fintype κ] in
theorem real_basis_coordinates_transfer (x : ℝ ⊗[ℚ] V) :
    (fun i => (e.baseChange ℝ).repr x i) =
      (fun i j => (e.repr (b j) i : ℝ)) *ᵥ (fun j => (b.baseChange ℝ).repr x j) := by
  classical
  funext i
  conv_lhs => rw [← (b.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  change (∑ j, (b.baseChange ℝ).repr x j * (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i) = _
  have he (j : ι) : (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i = (e.repr (b j) i : ℝ) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simp
  simp only [he, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype κ] in
theorem real_basis_coordinates_bound {H : ℕ} {B : ℝ}
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ B) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ (Fintype.card ι : ℝ) * H * B := by
  have hcoord := congrFun (real_basis_coordinates_transfer b e x) i
  rw [hcoord]
  calc
    _ ≤ ∑ j, |(e.repr (b j) i : ℝ) * (b.baseChange ℝ).repr x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, (H : ℝ) * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hentries i j).abs_real_le (hx j) (abs_nonneg _) (Nat.cast_nonneg H)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem real_basis_coordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun j => (b.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun i => (e.baseChange ℝ).repr x i) ∈
      realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  rw [real_basis_coordinates_transfer b e x]
  exact real_matrix_denominator_grid (fun i j => e.repr (b j) i) l _ hx

theorem real_basis_transfer_denominator {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H) :
    (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
  intro i j
  exact (show ((e.repr (b j) i).den : ℝ) ≤ H by exact_mod_cast (hentries i j).2).trans
    (hHp.trans (Real.exp_le_exp.mpr (by simp)))

omit [Fintype κ] in
theorem real_basis_coordinates_exp_bound {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ Real.exp p) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (Fintype.card ι : ℝ) ≤ Real.exp p := hι.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ (Fintype.card ι : ℝ) * H * Real.exp p := real_basis_coordinates_bound b e hentries x hx i
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (mul_le_mul hdim hHp (Nat.cast_nonneg H) (Real.exp_nonneg p))
        (Real.exp_nonneg p)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

section

namespace Erdos3
open scoped Matrix

theorem exists_rationalTaggedSpanProjection
    {J : Type*} [Fintype J] {r : ℕ} (g : Fin r → J → ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hr : (r : ℝ) ≤ p) (hg : ∀ a j, rationalLogHeight (g a j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card J ∧
      ∃ Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ),
        LinearMap.ker Q = Submodule.span ℝ (Set.range (fun a j => (g a j : ℝ))) ∧
        (∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖) ∧
        ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
          ∀ x : J → ℤ, ∃ z : Fin d → ℤ,
            ∀ i, (z i : ℝ) = (D : ℝ) * Q (fun j => (x j : ℝ)) i := by
  classical
  have hheight : ∀ j a, RationalHeightLE (g a j) ⌊Real.exp p⌋₊ := by
    intro j a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff (g a j) p).mp (hg a j)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  obtain ⟨d, hd, M, S, hker, hMS, hM, hS⟩ :=
    exists_quotient_presentation_exp_height (fun j a => g a j)
      ((Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)) hheight
      hp hJ (by simpa using hr) (Nat.floor_le (Real.exp_nonneg p))
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa using (Nat.cast_le.mpr hd).trans hJ
  let Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Matrix.mulVecLin (fun i j => (M i j : ℝ))
  have hentry : ∀ i j, |(M i j : ℝ)| ≤ Real.exp ((p + 2) ^ 7) :=
    fun i j => (rational_abs_real_le_numerator (M i j)).trans (hM i j).1
  have hbound : ∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖ := by
    intro x i
    have hb := abs_matrix_mulVec_le (fun i j => (M i j : ℝ))
      ⟨Real.exp ((p + 2) ^ 7), Real.exp_nonneg _⟩ hentry x i
    exact hb.trans (mul_le_mul_of_nonneg_right
      (matrix_weighted_factor_le_exp_power (Fintype.card J) hp hJ 7 (by decide))
      (norm_nonneg x))
  refine ⟨d, hd, Q, ?_, hbound, matrixDenominator M, matrixDenominator_pos M,
    matrixDenominator_le_exp_power M hp 7 hdp hJ (fun i j => (hM i j).2), ?_⟩
  · exact rationalMatrix_real_ker_eq_span (fun j a => g a j) M hker
  · intro x
    have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
      ⟨x, by ext j; simp⟩
    obtain ⟨z, hz⟩ := real_matrix_denominator_grid M 1 (fun j => (x j : ℝ)) hx
    refine ⟨z, fun i => ?_⟩
    change (z i : ℝ) = (matrixDenominator M : ℝ) *
      ((fun i j => (M i j : ℝ)) *ᵥ (fun j => (x j : ℝ))) i
    simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using congrFun hz i

end Erdos3

end

end OAI
