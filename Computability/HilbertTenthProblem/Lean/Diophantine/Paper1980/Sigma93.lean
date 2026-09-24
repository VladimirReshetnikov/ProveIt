import Diophantine.Paper1980.Mask93
import Diophantine.Paper1980.Bound93

/-!
# `σ` agrees with the coefficient sum of `D(T) C(T)²` below `B^K` (Section 4)

With `λ = Σ_{h<2L} B^h` (from `λ(B − 1) = B^{2L} − 1`), `e = e₀(B) =
Σ_{h<K} (1 + [X^h]D) B^h` and `q = B^L`, the equation
`σ = (λ − e)(q − C²)` gives

  `σ = Σ_{p<K} [X^p](D · C²) · B^p + B^K · High`

for some integer `High` (`sigma_decomp`).  The file also records the
coefficient bound `|[X^p](D · C_main²)| ≤ D₁ · (x + Σ zᵢ)²` for nonnegative
`x, z` (`abs_coeff_le`).
-/

namespace Jones1980

namespace Iso

open Polynomial Layout Finset

noncomputable section

/-- Splitting a coefficient sum at `K`. -/
theorem sum_range_split (a : ℕ → ℤ) (B : ℤ) {K N : ℕ} (hKN : K ≤ N) :
    ∑ p ∈ range N, a p * B ^ p =
      ∑ p ∈ range K, a p * B ^ p + B ^ K * ∑ p ∈ range (N - K), a (K + p) * B ^ p := by
  obtain ⟨d, rfl⟩ : ∃ d, N = K + d := ⟨N - K, by omega⟩
  rw [Nat.add_sub_cancel_left, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [pow_add]; ring

/-- The value of a polynomial is its coefficient sum below `K` plus a multiple of `B^K`. -/
theorem eval_eq_sum_split (P : ℤ[X]) (B : ℤ) (K : ℕ) :
    ∃ High : ℤ, P.eval B = ∑ p ∈ range K, P.coeff p * B ^ p + B ^ K * High := by
  have hn : P.natDegree < P.natDegree + K + 1 := by omega
  rw [eval_eq_sum_range' hn]
  exact ⟨_, sum_range_split _ _ (by omega)⟩

/-- `λ = Σ_{h<2L} B^h` from the geometric equation. -/
theorem lam_eq_geom {B lam L : ℕ} (hB : 2 ≤ B) (hlam : lam * (B - 1) = B ^ (2 * L) - 1) :
    lam = ∑ h ∈ range (2 * L), B ^ h := by
  have h := sum_pred_mul_pow (by omega : 1 ≤ B) (2 * L)
  have h' : (∑ h ∈ range (2 * L), B ^ h) * (B - 1) = B ^ (2 * L) - 1 := by
    rw [Finset.sum_mul]
    have : ∑ i ∈ range (2 * L), B ^ i * (B - 1) = ∑ i ∈ range (2 * L), (B - 1) * B ^ i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) (hlam.trans h'.symm)

section Decomp

variable {m s : ℕ} (rows : Fin s → Row m) (P5 P7 : Finset (Fin m))

/-- `D` has degree below `K`. -/
theorem natDegree_D_lt (hs : 1 ≤ s) : (D m s rows P5 P7).natDegree < K m s := by
  have hK : 3 ≤ K m s := by unfold K; omega
  have : (D m s rows P5 P7).natDegree ≤ K m s - 1 :=
    natDegree_le_iff_coeff_eq_zero.2 fun N hN => coeff_D_eq_zero_of_ge rows P5 P7 hs N (by omega)
  omega

/-- `σ = Σ_{p<K} [X^p](D · C²) B^p + B^K · High`. -/
theorem sigma_decomp {B L lam e q x g σ : ℕ} (hs : 1 ≤ s) (hB : 2 ≤ B) (hKL : K m s ≤ L)
    (hlam : lam * (B - 1) = B ^ (2 * L) - 1)
    (he : (e : ℤ) = ∑ h ∈ range (K m s), (1 + (D m s rows P5 P7).coeff h) * (B : ℤ) ^ h)
    (hq : q = B ^ L) (Cf : ℤ[X]) (hC : ((x + g : ℕ) : ℤ) = Cf.eval (B : ℤ))
    (hσ : (σ : ℤ) = ((lam : ℤ) - e) * (q - ((x : ℤ) + g) ^ 2)) :
    ∃ High : ℤ, (σ : ℤ) =
      ∑ p ∈ range (K m s), (D m s rows P5 P7 * Cf ^ 2).coeff p * (B : ℤ) ^ p +
        (B : ℤ) ^ (K m s) * High := by
  set Dp := D m s rows P5 P7 with hDp
  set K' := K m s with hK'
  set SK : ℤ := ∑ h ∈ range K', (B : ℤ) ^ h with hSK
  set G : ℤ := ∑ h ∈ range (2 * L - K'), (B : ℤ) ^ h with hG
  have hlamZ : (lam : ℤ) = ∑ h ∈ range (2 * L), (B : ℤ) ^ h := by
    rw [lam_eq_geom hB hlam]; push_cast; rfl
  have hsplit := sum_range_split (fun _ => (1 : ℤ)) (B : ℤ) (K := K') (N := 2 * L) (by omega)
  simp only [one_mul] at hsplit
  have hlam' : (lam : ℤ) = SK + (B : ℤ) ^ K' * G := by rw [hlamZ, hsplit]
  have hDeval : Dp.eval (B : ℤ) = ∑ h ∈ range K', Dp.coeff h * (B : ℤ) ^ h :=
    eval_eq_sum_range' (natDegree_D_lt rows P5 P7 hs) _
  have he' : (e : ℤ) = SK + Dp.eval (B : ℤ) := by
    rw [he, hDeval, hSK, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _; ring
  have hq' : (q : ℤ) = (B : ℤ) ^ K' * B ^ (L - K') := by
    rw [hq]; push_cast; rw [← pow_add]; congr 1; omega
  have hC' : (x : ℤ) + g = Cf.eval (B : ℤ) := by exact_mod_cast hC
  obtain ⟨High2, hH2⟩ := eval_eq_sum_split (Dp * Cf ^ 2) (B : ℤ) K'
  rw [eval_mul, eval_pow] at hH2
  refine ⟨High2 + (G * ((B : ℤ) ^ K' * B ^ (L - K')) - G * Cf.eval (B : ℤ) ^ 2 -
    Dp.eval (B : ℤ) * B ^ (L - K')), ?_⟩
  rw [hσ, hlam', he', hq', hC']
  linear_combination hH2

/-- The coefficients of `C_main²` are nonnegative for nonnegative digits. -/
theorem coeff_Cmain_sq_nonneg (x : ℤ) (z : Fin m → ℤ) (hx : 0 ≤ x) (hz : ∀ i, 0 ≤ z i)
    (w : ℕ) : 0 ≤ (Cmain m x z ^ 2).coeff w := by
  rw [coeff_Cmain_sq]
  refine add_nonneg (add_nonneg ?_ (Finset.sum_nonneg fun i _ => ?_))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_)
  · split_ifs
    · exact sq_nonneg x
    · exact le_rfl
  · split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) hx) (hz i)
    · exact le_rfl
  · split_ifs
    · exact mul_nonneg (hz i) (hz k)
    · exact le_rfl

theorem eval_one_Cmain (x : ℤ) (z : Fin m → ℤ) : (Cmain m x z).eval 1 = x + ∑ i, z i := by
  unfold Cmain; simp [eval_finsetSum]

/-- `|[X^p](D · C_main²)| ≤ D₁ · (x + Σ zᵢ)²`. -/
theorem abs_coeff_le (x : ℤ) (z : Fin m → ℤ) (hx : 0 ≤ x) (hz : ∀ i, 0 ≤ z i) (p : ℕ) :
    |(D m s rows P5 P7 * Cmain m x z ^ 2).coeff p| ≤
      absSum (D m s rows P5 P7) * (x + ∑ i, z i) ^ 2 := by
  have := abs_coeff_mul_le (D m s rows P5 P7) (Cmain m x z ^ 2)
    (coeff_Cmain_sq_nonneg x z hx hz) p
  rwa [eval_pow, eval_one_Cmain] at this

end Decomp

end

end Iso

end Jones1980
