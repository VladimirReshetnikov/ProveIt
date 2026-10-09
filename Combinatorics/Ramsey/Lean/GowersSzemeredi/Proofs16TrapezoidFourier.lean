import GowersSzemeredi.Proofs16Trapezoid

/-! Fourier decay of the discrete trapezoid: brick B of [49]'s Proposition 26.

* `centeredBall_eq_image`: for `2a < N`, the ball `I_a` is the progression
  `{−a + i : i ≤ 2a}`.
* `fourier_centeredBall_le`: for `ξ ≠ 0`, `|Î_a(ξ)| ≤ N/(2|ξ|)`
  (`interval_exponential_sum_le`).
* `fourier_trapezoid`: `ĝ(ξ) = Î_a(ξ)·Î_c(ξ)/|I_c|`, the convolution
  theorem for the trapezoid.
* `fourier_trapezoid_le`: for `2a < N`, `2c < N` and `ξ ≠ 0`,
  `|ĝ(ξ)| ≤ (N/(2|ξ|))² / |I_c|`, i.e. decay like `1/ξ²`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The ball is a progression when it does not wrap. -/
theorem centeredBall_eq_image {N : Nat} [NeZero N] {a : Nat} (ha : 2 * a < N) :
    centeredBall N a = (Finset.range (2 * a + 1)).image fun i : Nat => -(a : ZMod N) + i := by
  ext t
  simp only [centeredBall, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range]
  constructor
  · intro ht
    set v := t.valMinAbs
    have hv : v.natAbs ≤ a := ht
    refine ⟨(v + a).toNat, by omega, ?_⟩
    have hcast : (((v + a).toNat : Nat) : ZMod N) = ((v + a : Int) : ZMod N) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hcast]
    push_cast
    rw [ZMod.coe_valMinAbs]
    ring
  · rintro ⟨i, hi, rfl⟩
    show (-(a : ZMod N) + i).valMinAbs.natAbs ≤ a
    have hspec : (-(a : ZMod N) + i).valMinAbs = (i : Int) - a := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨by push_cast; ring, ?_, ?_⟩ <;> omega
    rw [hspec]
    omega

/-- **Fourier transform of a ball.** -/
theorem fourier_centeredBall_le {N : Nat} [NeZero N] {a : Nat} (ha : 2 * a < N) {ξ : ZMod N}
    (hξ : ξ ≠ 0) :
    ‖fourier (indicator (centeredBall N a)) ξ‖ ≤ N / (2 * (centeredAbs ξ : Real)) := by
  have hsum : fourier (indicator (centeredBall N a)) ξ =
      ∑ i ∈ Finset.range (2 * a + 1), exponential ((-(a : ZMod N) + (i : ZMod N)) * (-ξ)) := by
    unfold fourier
    rw [ZMod.dft_apply]
    have : ∀ j : ZMod N, ZMod.stdAddChar (-(j * ξ)) • indicator (centeredBall N a) j =
        if j ∈ centeredBall N a then exponential (j * (-ξ)) else 0 := by
      intro j
      unfold indicator exponential
      split_ifs <;> simp [mul_neg]
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, centeredBall_eq_image ha, Finset.sum_image]
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have h : ((i : Nat) : ZMod N) = ((j : Nat) : ZMod N) := by simpa using hij
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  rw [hsum]
  have hξ' : -ξ ≠ 0 := neg_ne_zero.mpr hξ
  have := interval_exponential_sum_le hξ' (-(a : ZMod N)) (2 * a + 1)
  rwa [centeredAbs_neg] at this

/-- The trapezoid fibre is a ball condition. -/
theorem trapezoid_complex {N : Nat} [NeZero N] (a c : Nat) (t : ZMod N) :
    ((trapezoid a c t : Real) : Complex) =
      ((centeredBall N c).card : Complex)⁻¹ *
        ∑ s ∈ centeredBall N a, indicator (centeredBall N c) (t - s) := by
  unfold trapezoid
  push_cast
  rw [div_eq_inv_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  unfold indicator centeredBall
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The transform of an indicator is a sum over the set. -/
theorem fourier_indicator_eq_sum {N : Nat} [NeZero N] (A : Finset (ZMod N)) (ξ : ZMod N) :
    fourier (indicator A) ξ = ∑ s ∈ A, ZMod.stdAddChar (-(s * ξ)) := by
  unfold fourier indicator
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The convolution theorem for the trapezoid.** -/
theorem fourier_trapezoid {N : Nat} [NeZero N] (a c : Nat) (ξ : ZMod N) :
    fourier (fun t => ((trapezoid a c t : Real) : Complex)) ξ =
      ((centeredBall N c).card : Complex)⁻¹ *
        (fourier (indicator (centeredBall N a)) ξ * fourier (indicator (centeredBall N c)) ξ) := by
  rw [fourier_indicator_eq_sum, fourier_indicator_eq_sum]
  have hshift : ∀ s : ZMod N, (∑ t : ZMod N, ZMod.stdAddChar (-(t * ξ)) *
      indicator (centeredBall N c) (t - s)) =
      ZMod.stdAddChar (-(s * ξ)) * ∑ u ∈ centeredBall N c, ZMod.stdAddChar (-(u * ξ)) := by
    intro s
    rw [← fourier_indicator_eq_sum]
    unfold fourier
    rw [ZMod.dft_apply, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.subRight s)
    intro t
    simp only [Equiv.subRight_apply, smul_eq_mul]
    rw [show -(t * ξ) = -(s * ξ) + -((t - s) * ξ) by ring, AddChar.map_add_eq_mul]
    ring
  unfold fourier
  rw [ZMod.dft_apply]
  simp only [trapezoid_complex, smul_eq_mul]
  calc ∑ t : ZMod N, ZMod.stdAddChar (-(t * ξ)) *
        (((centeredBall N c).card : Complex)⁻¹ *
          ∑ s ∈ centeredBall N a, indicator (centeredBall N c) (t - s))
      = ((centeredBall N c).card : Complex)⁻¹ *
          ∑ s ∈ centeredBall N a, ∑ t : ZMod N,
            ZMod.stdAddChar (-(t * ξ)) * indicator (centeredBall N c) (t - s) := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ = _ := by
        rw [Finset.sum_congr rfl fun s _ => hshift s, ← Finset.sum_mul]

/-- **Decay of the trapezoid's transform.** -/
theorem fourier_trapezoid_le {N : Nat} [NeZero N] {a c : Nat} (ha : 2 * a < N) (hc : 2 * c < N)
    {ξ : ZMod N} (hξ : ξ ≠ 0) :
    ‖fourier (fun t => ((trapezoid a c t : Real) : Complex)) ξ‖ ≤
      (N / (2 * (centeredAbs ξ : Real))) ^ 2 / (centeredBall N c).card := by
  rw [fourier_trapezoid, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := fourier_centeredBall_le ha hξ
  have h2 := fourier_centeredBall_le hc hξ
  have hcpos : (0 : Real) < (centeredBall N c).card := by
    have : (0 : ZMod N) ∈ centeredBall N c := by
      simp [centeredBall, centeredAbs]
    exact_mod_cast Finset.card_pos.mpr ⟨0, this⟩
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right hcpos, sq]
  exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)

end LeanProofs.GowersSzemeredi
