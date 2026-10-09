import GowersSzemeredi.Proofs16ProductApproximation

/-! An explicit cutoff for the bounded-span theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A rational upper bound for a product of small relative errors. -/
theorem one_add_pow_mul_one_sub_le_one {eta : Real} (heta : 0 ≤ eta) (m : Nat) :
    (1 + eta)^m * (1 - m * eta) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (1 + eta) * (1 - ((m : Real) + 1) * eta) ≤ 1 - m * eta := by
      have : 0 ≤ ((m : Real) + 1) * eta^2 := by positivity
      nlinarith only [this]
    calc
      (1 + eta)^(m + 1) * (1 - (m + 1 : Nat) * eta) =
          (1 + eta)^m * ((1 + eta) * (1 - ((m : Real) + 1) * eta)) := by rw [pow_succ]; push_cast; ring
      _ ≤ (1 + eta)^m * (1 - m * eta) := mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ 1 := ih

/-- Linear product error when the total scalar error is at most one half. -/
theorem one_add_pow_sub_one_le_twice {eta : Real} (heta : 0 ≤ eta) (m : Nat)
    (hsmall : (m : Real) * eta ≤ 1 / 2) :
    (1 + eta)^m - 1 ≤ 2 * m * eta := by
  have h := one_add_pow_mul_one_sub_le_one heta m
  have hden : 0 < 1 - (m : Real) * eta := by linarith
  have hrational : (1 + eta)^m ≤ 1 / (1 - m * eta) := (le_div_iff₀ hden).mpr h
  have hbound : 1 / (1 - (m : Real) * eta) ≤ 1 + 2 * m * eta := by
    apply (div_le_iff₀ hden).mpr
    have hnonneg : 0 ≤ (m : Real) * eta := by positivity
    nlinarith
  linarith

/-- An explicit cutoff makes the product approximation error at most
one quarter of epsilon. -/
theorem trapezoid_product_cutoff_budget {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (c R : Nat) {epsilon : Real}
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hR : 8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card) ≤ R + 1) :
    (1 + N / ((centeredBall N c).card * (R + 1 : Real)))^K.card - 1 ≤ epsilon / 4 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hC : (0 : Real) < (centeredBall N c).card := by
    have hz : (0 : ZMod N) ∈ centeredBall N c := by simp [centeredBall, centeredAbs]
    exact_mod_cast Finset.card_pos.mpr ⟨0, hz⟩
  let eta : Real := N / ((centeredBall N c).card * (R + 1 : Real))
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hscale : 8 * (K.card + 1 : Real) * N ≤ (R + 1 : Real) * (epsilon * (centeredBall N c).card) :=
    (div_le_iff₀ (mul_pos heps hC)).mp hR
  have hscalar : ((K.card : Real) + 1) * eta ≤ epsilon / 8 := by
    dsimp only [eta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show (0 : Real) < (centeredBall N c).card * (R + 1 : Real) by positivity)).mpr
    nlinarith only [hscale]
  have hsmall : (K.card : Real) * eta ≤ 1 / 2 := by linarith
  have h := one_add_pow_sub_one_le_twice heta K.card hsmall
  change (1 + eta)^K.card - 1 ≤ epsilon / 4
  linarith

/-- Bounded-span containment with a concrete cutoff and only a numerical
boundary-band condition. -/
theorem large_bohr_fourier_mem_explicit_boundedSpan {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) {a c : Nat} (hca : c ≤ a)
    (ha : 2 * a < N) (hc : 2 * c < N) {epsilon : Real}
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hband : K.card * (4 * (c : Real) + 2) ≤ epsilon / 2 * N)
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier (indicator (bohr K ((a : Real) / N))) xi‖) :
    xi ∈ boundedFrequencySpan (fun gamma : K => (gamma : ZMod N))
      ⌈8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card)⌉₊ := by
  let R := ⌈8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card)⌉₊
  apply large_bohr_fourier_mem_boundedSpan_of_budget K hca ha hc R _ hlarge
  have hR : 8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card) ≤ R + 1 := by
    have h := Nat.le_ceil (8 * (K.card + 1 : Real) * N / (epsilon * (centeredBall N c).card))
    change _ ≤ (R : Real) at h
    linarith
  have herr := trapezoid_product_cutoff_budget K c R heps heps1 hR
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hscaled := mul_le_mul_of_nonneg_right herr hNR.le
  have hpos := mul_pos heps hNR
  linarith

end LeanProofs.GowersSzemeredi
