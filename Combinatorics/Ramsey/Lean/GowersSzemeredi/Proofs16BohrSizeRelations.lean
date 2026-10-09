import GowersSzemeredi.Proofs16BohrSpectrumBudget
import GowersSzemeredi.Proofs16SpectrumPairSumset

/-! The size of a Bohr set as a weighted count of linear relations: [49]
Proposition 23 in `ℤ/N`, with a radius for each frequency.

For a tuple of frequencies `γ : ι → ℤ/N`, [49] Proposition 23 writes
`|B(γ; ρ)|` as `|G|·Σ_{a ∈ [−K,K]^ι} 1(Σ aᵢγᵢ = 0) Πᵢ c_{aᵢ}`, up to
`2ε|G|`. It assumes the weak regularity `|B(γ; ρ+η) ∖ B(γ; ρ)| ≤ ε|G|`.
The coefficients `c_a` depend only on the parameters, never on `γ`. That
is what the algebraic regularity lemma (Theorem 33, Claim 34) uses:
relations among the frequencies alone determine the Bohr set's size.

Here every frequency carries its own integer radius `aᵢ`, and
`mixedBohr γ a = {x : |γᵢx| ≤ aᵢ for all i}`. Mixed radii are needed for
the pattern graph of the seven-operator completion, whose edges are
`B(F; θ/2) ∩ B(V(t); θ/8)`. In `ℤ/N` the coefficients are the normalized
Fourier coefficients of the discrete trapezoid,
`trapezoidRelationCoeff a c r = N⁻¹·ĝ(r)` with `g = 1_{I_a} * 1_{I_c}/|I_c|`.
They depend on `N`, `a` and `c` only. The uniform-radius statements are
the case of constant `a` (`mixedBohr_const`).

* `sum_boundedCharacterProduct`: summing a product of truncated character
  series over `ℤ/N` leaves `N` times the weighted number of coefficient
  vectors `v` with `Σ vᵢγᵢ = 0` (orthogonality).
* `trapezoid_mixed_uniform_truncation`: the per-index trapezoid product is
  uniformly within `(1 + N/(|I_c|(R+1)))^|ι| − 1` of its truncation.
  Tuples allow repeated frequencies, as in Claim 34's families
  `Γ ∪ {L₁(y),…}`.
* `trapezoid_mixed_sum_sandwich`: for `c ≤ aᵢ`,
  `|mixedBohr γ (a−c)| ≤ Σ_x Πᵢ g_{aᵢ}(γᵢx) ≤ |mixedBohr γ (a+c)|`.
* `bohr_card_approx_relations_mixed` (Proposition 23): under weak
  regularity `|mixedBohr γ (a+c)| ≤ |mixedBohr γ (a−c)| + εN` and the
  truncation budget, `|mixedBohr γ (a−c)|` is within `2εN` of
  `N·relationWeightMixed γ a c R`.
* `bohr_card_approx_relations`, `bohr_card_approx_relations_explicit`: the
  uniform-radius case, the latter with the explicit cutoff
  `R + 1 ≥ 4(|ι|+1)N/(ε|I_c|)` for `0 < ε ≤ 1`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The normalized Fourier coefficient of the discrete trapezoid. -/
def trapezoidRelationCoeff {N : Nat} [NeZero N] (a c : Nat) (r : ZMod N) : Complex :=
  (N : Complex)⁻¹ * fourier (fun t => ((trapezoid a c t : Real) : Complex)) r

/-- The Bohr set of a tuple with a radius for each frequency. -/
def mixedBohr {N : Nat} [NeZero N] {ι : Type*} [Fintype ι] (γ : ι → ZMod N) (a : ι → Nat) :
    Finset (ZMod N) :=
  Finset.univ.filter fun x => ∀ i, centeredAbs (γ i * x) ≤ a i

/-- The weighted count of bounded linear relations among the frequencies,
with per-index trapezoid coefficients. -/
def relationWeightMixed {N : Nat} [NeZero N] {ι : Type*} [Fintype ι] (γ : ι → ZMod N)
    (a : ι → Nat) (c R : Nat) : Complex :=
  ∑ v : ι → centeredBall N R, (∏ i, trapezoidRelationCoeff (a i) c (v i : ZMod N)) *
    (if ∑ i, (v i : ZMod N) * γ i = 0 then 1 else 0)

/-- The weighted count of bounded linear relations at a common radius. -/
def relationWeight {N : Nat} [NeZero N] {ι : Type*} [Fintype ι] (γ : ι → ZMod N)
    (a c R : Nat) : Complex :=
  relationWeightMixed γ (fun _ => a) c R

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

theorem mem_mixedBohr {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    {γ : ι → ZMod N} {a : ι → Nat} {x : ZMod N} :
    x ∈ mixedBohr γ a ↔ ∀ i, centeredAbs (γ i * x) ≤ a i := by
  simp [mixedBohr]

/-- At a common radius the mixed Bohr set is the ordinary one. -/
theorem mixedBohr_const {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (r : Nat) :
    mixedBohr γ (fun _ => r) = bohr (Finset.univ.image γ) ((r : Real) / N) := by
  ext x
  rw [mem_mixedBohr, mem_bohr_image_iff]

/-- **The per-index trapezoid product sandwiches the mixed Bohr sets.** -/
theorem trapezoid_mixed_sum_sandwich {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (a : ι → Nat) (c : Nat) (hca : ∀ i, c ≤ a i) :
    ((mixedBohr γ (fun i => a i - c)).card : Real) ≤
        ∑ x : ZMod N, ∏ i, trapezoid (a i) c (γ i * x) ∧
      ∑ x : ZMod N, ∏ i, trapezoid (a i) c (γ i * x) ≤
        ((mixedBohr γ (fun i => a i + c)).card : Real) := by
  have hP0 : ∀ x : ZMod N, 0 ≤ ∏ i, trapezoid (a i) c (γ i * x) :=
    fun x => Finset.prod_nonneg fun i _ => trapezoid_nonneg _ c _
  have hP1 : ∀ x : ZMod N, ∏ i, trapezoid (a i) c (γ i * x) ≤ 1 :=
    fun x => Finset.prod_le_one (fun i _ => trapezoid_nonneg _ c _)
      fun i _ => trapezoid_le_one _ c _
  constructor
  · calc ((mixedBohr γ (fun i => a i - c)).card : Real)
        = ∑ x ∈ mixedBohr γ (fun i => a i - c), ∏ i, trapezoid (a i) c (γ i * x) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          apply Finset.sum_congr rfl
          intro x hx
          rw [mem_mixedBohr] at hx
          exact (Finset.prod_eq_one fun i _ =>
            trapezoid_eq_one _ c _ (by have := hx i; have := hca i; omega)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => hP0 x)
  · rw [← Finset.sum_subset (Finset.subset_univ (mixedBohr γ (fun i => a i + c)))]
    · calc _ ≤ ∑ _x ∈ mixedBohr γ (fun i => a i + c), (1 : Real) :=
            Finset.sum_le_sum fun x _ => hP1 x
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · intro x _ hx
      rw [mem_mixedBohr] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (trapezoid_eq_zero _ c _ hi)

/-- **Uniform truncation of the per-index trapezoid product.** -/
theorem trapezoid_mixed_uniform_truncation {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (a : ι → Nat) {c : Nat} (ha : ∀ i, 2 * a i < N) (hc : 2 * c < N)
    (R : Nat) (x : ZMod N) :
    ‖((∏ i, trapezoid (a i) c (γ i * x) : Real) : Complex) -
      boundedCharacterProduct γ R (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x‖ ≤
      (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 := by
  have heq : boundedCharacterProduct γ R
      (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x =
      ∏ i, centeredFourierTruncation
        (fun t => ((trapezoid (a i) c t : Real) : Complex)) R (γ i * x) := by
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
    exact trapezoid_uniform_truncation (ha i) hc R (γ i * x)

/-- **[49] Proposition 23 in `ℤ/N`, with a radius for each frequency.** -/
theorem bohr_card_approx_relations_mixed {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) (a : ι → Nat) {c R : Nat} (hca : ∀ i, c ≤ a i)
    (ha : ∀ i, 2 * a i < N) (hc : 2 * c < N) {ε : Real}
    (hband : ((mixedBohr γ (fun i => a i + c)).card : Real) ≤
      (mixedBohr γ (fun i => a i - c)).card + ε * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ ε) :
    ‖(((mixedBohr γ (fun i => a i - c)).card : Real) : Complex) -
      N * relationWeightMixed γ a c R‖ ≤ 2 * ε * N := by
  obtain ⟨hlow, hup⟩ := trapezoid_mixed_sum_sandwich γ a c hca
  set Bin := ((mixedBohr γ (fun i => a i - c)).card : Real)
  set P := ∑ x : ZMod N, ∏ i, trapezoid (a i) c (γ i * x)
  have hQ : ∑ x : ZMod N,
      boundedCharacterProduct γ R (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x =
      N * relationWeightMixed γ a c R := by
    rw [sum_boundedCharacterProduct]
    rfl
  have hPQ : ‖((P : Real) : Complex) - N * relationWeightMixed γ a c R‖ ≤ ε * N := by
    rw [← hQ]
    have hcast : ((P : Real) : Complex) =
        ∑ x : ZMod N, ((∏ i, trapezoid (a i) c (γ i * x) : Real) : Complex) := by
      simp only [P]; push_cast; rfl
    rw [hcast, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ x : ZMod N, ‖((∏ i, trapezoid (a i) c (γ i * x) : Real) : Complex) -
          boundedCharacterProduct γ R
            (fun i r => trapezoidRelationCoeff (a i) c (r : ZMod N)) x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _x : ZMod N, ε := Finset.sum_le_sum fun x _ =>
          (trapezoid_mixed_uniform_truncation γ a ha hc R x).trans htrunc
      _ = ε * N := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hBP : ‖((Bin : Real) : Complex) - ((P : Real) : Complex)‖ ≤ ε * N := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc _ = ‖(((Bin : Real) : Complex) - ((P : Real) : Complex)) +
        (((P : Real) : Complex) - N * relationWeightMixed γ a c R)‖ := by ring_nf
    _ ≤ ‖((Bin : Real) : Complex) - ((P : Real) : Complex)‖ +
        ‖((P : Real) : Complex) - N * relationWeightMixed γ a c R‖ := norm_add_le _ _
    _ ≤ ε * N + ε * N := add_le_add hBP hPQ
    _ = 2 * ε * N := by ring

/-- **[49] Proposition 23 in `ℤ/N`.** -/
theorem bohr_card_approx_relations {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (γ : ι → ZMod N) {a c R : Nat} (hca : c ≤ a) (ha : 2 * a < N) (hc : 2 * c < N)
    {ε : Real}
    (hband : ((bohr (Finset.univ.image γ) (((a + c : Nat) : Real) / N)).card : Real) ≤
      (bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card + ε * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ ε) :
    ‖(((bohr (Finset.univ.image γ) (((a - c : Nat) : Real) / N)).card : Real) : Complex) -
      N * relationWeight γ a c R‖ ≤ 2 * ε * N := by
  rw [← mixedBohr_const, ← mixedBohr_const] at hband
  rw [← mixedBohr_const]
  exact bohr_card_approx_relations_mixed γ (fun _ => a) (fun _ => hca) (fun _ => ha) hc
    hband htrunc

/-- The explicit cutoff makes the truncation error at most `ε`. -/
theorem truncation_budget_of_cutoff {N : Nat} [NeZero N] {c R m : Nat} {ε : Real}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 4 * (m + 1 : Real) * N / (ε * (centeredBall N c).card) ≤ R + 1) :
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ m - 1 ≤ ε := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hIc : (0 : Real) < (centeredBall N c).card := by
    have hz : (0 : ZMod N) ∈ centeredBall N c := by simp [centeredBall, centeredAbs]
    exact_mod_cast Finset.card_pos.mpr ⟨0, hz⟩
  obtain ⟨η, hη⟩ : ∃ η : Real, η = N / ((centeredBall N c).card * (R + 1 : Real)) :=
    ⟨_, rfl⟩
  rw [← hη]
  have hR1 : (0 : Real) < R + 1 := by positivity
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hmη : (m : Real) * η ≤ ε / 4 := by
    rw [hη]
    have hm : (m : Real) ≤ m + 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at hR
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : (0 : Real) ≤ 4 * N)]
  have hsmall : (m : Real) * η ≤ 1 / 2 := by linarith
  have h2 := one_add_pow_sub_one_le_twice hη0 m hsmall
  linarith

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
  exact truncation_budget_of_cutoff hε hε1 hR

end LeanProofs.GowersSzemeredi
