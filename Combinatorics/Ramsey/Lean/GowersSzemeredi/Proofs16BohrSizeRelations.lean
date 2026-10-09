import GowersSzemeredi.Proofs16BohrSpectrumBudget
import GowersSzemeredi.Proofs16SpectrumPairSumset

/-! The size of a Bohr set as a weighted count of linear relations: [49]
Proposition 23 in `ℤ/N`.

For a tuple of frequencies `γ : ι → ℤ/N`, [49] Proposition 23 writes
`|B(γ; ρ)|` as `|G|·Σ_{a ∈ [−K,K]^ι} 1(Σ aᵢγᵢ = 0) Πᵢ c_{aᵢ}`, up to
`2ε|G|`. It assumes the weak regularity `|B(γ; ρ+η) ∖ B(γ; ρ)| ≤ ε|G|`.
The coefficients `c_a` depend only on the parameters, never on `γ`. That
is what the algebraic regularity lemma (Theorem 33, Claim 34) uses:
relations among the frequencies alone determine the Bohr set's size.

In `ℤ/N` the coefficients are the normalized Fourier coefficients of the
discrete trapezoid,
`trapezoidRelationCoeff a c r = N⁻¹·ĝ(r)` with `g = 1_{I_a} * 1_{I_c}/|I_c|`.
They depend on `N`, `a`, `c` only.

* `sum_boundedCharacterProduct`: summing a product of truncated character
  series over `ℤ/N` leaves `N` times the weighted number of coefficient
  vectors `v` with `Σ vᵢγᵢ = 0` (orthogonality).
* `trapezoid_tuple_uniform_truncation`: the trapezoid product over a tuple
  is uniformly within `(1 + N/(|I_c|(R+1)))^|ι| − 1` of its truncation.
  This is the tuple form of the Finset statement
  `trapezoid_product_uniform_truncation`. Tuples allow repeated
  frequencies, as in Claim 34's families `Γ ∪ {L₁(y),…}`.
* `trapezoid_tuple_sum_sandwich`: for `c ≤ a`,
  `|B(γ; (a−c)/N)| ≤ Σ_x Πᵢ g(γᵢx) ≤ |B(γ; (a+c)/N)|`.
* `bohr_card_approx_relations` (Proposition 23): under weak regularity
  `|B(γ;(a+c)/N)| ≤ |B(γ;(a−c)/N)| + εN` and the truncation budget,
  `|B(γ;(a−c)/N)|` is within `2εN` of `N·relationWeight γ a c R`.
* `bohr_card_approx_relations_explicit`: the same with the explicit cutoff
  `R + 1 ≥ 4(|ι|+1)N/(ε|I_c|)`, for `0 < ε ≤ 1`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The normalized Fourier coefficient of the discrete trapezoid. -/
def trapezoidRelationCoeff {N : Nat} [NeZero N] (a c : Nat) (r : ZMod N) : Complex :=
  (N : Complex)⁻¹ * fourier (fun t => ((trapezoid a c t : Real) : Complex)) r

/-- The weighted count of bounded linear relations among the frequencies. -/
def relationWeight {N : Nat} [NeZero N] {ι : Type*} [Fintype ι] (γ : ι → ZMod N)
    (a c R : Nat) : Complex :=
  ∑ v : ι → centeredBall N R, (∏ i, trapezoidRelationCoeff a c (v i : ZMod N)) *
    (if ∑ i, (v i : ZMod N) * γ i = 0 then 1 else 0)

/-- **Orthogonality applied to a product of truncated series.** -/
theorem sum_boundedCharacterProduct {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (R : Nat) (c : ι → centeredBall N R → Complex) :
    ∑ x : ZMod N, boundedCharacterProduct γ R c x =
      N * ∑ v : ι → centeredBall N R, (∏ i, c i (v i)) *
        (if ∑ i, (v i : ZMod N) * γ i = 0 then 1 else 0) := by
  simp_rw [boundedCharacterProduct_expansion]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum, sum_exponential_mul_eq_ite]
  split_ifs <;> ring

/-- Membership in the Bohr set of a tuple, at a grid radius. -/
theorem mem_bohr_image_iff {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (r : Nat) (x : ZMod N) :
    x ∈ bohr (Finset.univ.image γ) ((r : Real) / N) ↔ ∀ i, centeredAbs (γ i * x) ≤ r := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  unfold bohr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h i
    have := h (γ i) ⟨i, rfl⟩
    rw [div_mul_cancel₀ _ hNR.ne'] at this
    exact_mod_cast this
  · rintro h _ ⟨i, rfl⟩
    rw [div_mul_cancel₀ _ hNR.ne']
    exact_mod_cast h i

/-- **The trapezoid product of a tuple sandwiches its Bohr sets.** -/
theorem trapezoid_tuple_sum_sandwich {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) {a c : Nat} (hca : c ≤ a) :
    ((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) ≤
        ∑ x : ZMod N, ∏ i, trapezoid a c (γ i * x) ∧
      ∑ x : ZMod N, ∏ i, trapezoid a c (γ i * x) ≤
        ((bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)).card : Real) := by
  have hP0 : ∀ x : ZMod N, 0 ≤ ∏ i, trapezoid a c (γ i * x) :=
    fun x => Finset.prod_nonneg fun i _ => trapezoid_nonneg a c _
  have hP1 : ∀ x : ZMod N, ∏ i, trapezoid a c (γ i * x) ≤ 1 :=
    fun x => Finset.prod_le_one (fun i _ => trapezoid_nonneg a c _)
      fun i _ => trapezoid_le_one a c _
  constructor
  · calc ((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real)
        = ∑ x ∈ bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N),
            ∏ i, trapezoid a c (γ i * x) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          apply Finset.sum_congr rfl
          intro x hx
          rw [mem_bohr_image_iff] at hx
          exact (Finset.prod_eq_one fun i _ =>
            trapezoid_eq_one a c _ (by have := hx i; omega)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => hP0 x)
  · rw [← Finset.sum_subset (Finset.subset_univ
      (bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)))]
    · calc _ ≤ ∑ _x ∈ bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N), (1 : Real) :=
            Finset.sum_le_sum fun x _ => hP1 x
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · intro x _ hx
      rw [mem_bohr_image_iff] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (trapezoid_eq_zero a c _ hi)

/-- **Uniform truncation of the trapezoid product of a tuple.** -/
theorem trapezoid_tuple_uniform_truncation {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) {a c : Nat} (ha : 2 * a < N) (hc : 2 * c < N) (R : Nat) (x : ZMod N) :
    ‖((∏ i, trapezoid a c (γ i * x) : Real) : Complex) -
      boundedCharacterProduct γ R (fun _ r => trapezoidRelationCoeff a c (r : ZMod N)) x‖ ≤
      (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 := by
  have heq : boundedCharacterProduct γ R (fun _ r => trapezoidRelationCoeff a c (r : ZMod N)) x =
      ∏ i, centeredFourierTruncation
        (fun t => ((trapezoid a c t : Real) : Complex)) R (γ i * x) := by
    unfold boundedCharacterProduct centeredFourierTruncation trapezoidRelationCoeff
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_assoc]
  rw [heq, Complex.ofReal_prod, ← Finset.card_univ]
  apply norm_product_approximation
  · positivity
  · intro i _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (trapezoid_nonneg _ _ _)]
    exact trapezoid_le_one _ _ _
  · intro i _
    exact trapezoid_uniform_truncation ha hc R (γ i * x)

/-- **[49] Proposition 23 in `ℤ/N`.** -/
theorem bohr_card_approx_relations {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) {a c R : Nat} (hca : c ≤ a) (ha : 2 * a < N) (hc : 2 * c < N)
    {ε : Real}
    (hband : ((bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)).card : Real) ≤
      (bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card + ε * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ ε) :
    ‖(((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) : Complex) -
      N * relationWeight γ a c R‖ ≤ 2 * ε * N := by
  obtain ⟨hlow, hup⟩ := trapezoid_tuple_sum_sandwich γ hca
  set Bin := ((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real)
  set P := ∑ x : ZMod N, ∏ i, trapezoid a c (γ i * x)
  have hQ : ∑ x : ZMod N,
      boundedCharacterProduct γ R (fun _ r => trapezoidRelationCoeff a c (r : ZMod N)) x =
      N * relationWeight γ a c R := by
    rw [sum_boundedCharacterProduct]
    rfl
  have hPQ : ‖((P : Real) : Complex) - N * relationWeight γ a c R‖ ≤ ε * N := by
    rw [← hQ]
    have hcast : ((P : Real) : Complex) =
        ∑ x : ZMod N, ((∏ i, trapezoid a c (γ i * x) : Real) : Complex) := by
      simp only [P]; push_cast; rfl
    rw [hcast, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ x : ZMod N, ‖((∏ i, trapezoid a c (γ i * x) : Real) : Complex) -
          boundedCharacterProduct γ R (fun _ r => trapezoidRelationCoeff a c (r : ZMod N)) x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _x : ZMod N, ε := Finset.sum_le_sum fun x _ =>
          (trapezoid_tuple_uniform_truncation γ ha hc R x).trans htrunc
      _ = ε * N := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hBP : ‖((Bin : Real) : Complex) - ((P : Real) : Complex)‖ ≤ ε * N := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc _ = ‖(((Bin : Real) : Complex) - ((P : Real) : Complex)) +
        (((P : Real) : Complex) - N * relationWeight γ a c R)‖ := by ring_nf
    _ ≤ ‖((Bin : Real) : Complex) - ((P : Real) : Complex)‖ +
        ‖((P : Real) : Complex) - N * relationWeight γ a c R‖ := norm_add_le _ _
    _ ≤ ε * N + ε * N := add_le_add hBP hPQ
    _ = 2 * ε * N := by ring

/-- **Proposition 23 with an explicit cutoff.** -/
theorem bohr_card_approx_relations_explicit {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) {a c R : Nat} (hca : c ≤ a) (ha : 2 * a < N) (hc : 2 * c < N)
    {ε : Real} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hband : ((bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)).card : Real) ≤
      (bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card + ε * N)
    (hR : 4 * (Fintype.card ι + 1 : Real) * N / (ε * (centeredBall N c).card) ≤ R + 1) :
    ‖(((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) : Complex) -
      N * relationWeight γ a c R‖ ≤ 2 * ε * N := by
  apply bohr_card_approx_relations γ hca ha hc hband
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hIc : (0 : Real) < (centeredBall N c).card := by
    have hz : (0 : ZMod N) ∈ centeredBall N c := by simp [centeredBall, centeredAbs]
    exact_mod_cast Finset.card_pos.mpr ⟨0, hz⟩
  obtain ⟨η, hη⟩ : ∃ η : Real, η = N / ((centeredBall N c).card * (R + 1 : Real)) :=
    ⟨_, rfl⟩
  rw [← hη]
  have hR1 : (0 : Real) < R + 1 := by positivity
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  -- `m η ≤ ε/4`
  have hmη : (Fintype.card ι : Real) * η ≤ ε / 4 := by
    rw [hη]
    have hm : (Fintype.card ι : Real) ≤ Fintype.card ι + 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at hR
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : (0 : Real) ≤ 4 * N)]
  have hsmall : (Fintype.card ι : Real) * η ≤ 1 / 2 := by linarith
  have h2 := one_add_pow_sub_one_le_twice hη0 (Fintype.card ι) hsmall
  linarith

end LeanProofs.GowersSzemeredi
