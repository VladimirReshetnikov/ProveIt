import GowersSzemeredi.Proofs16TrapezoidFourier

/-! The finite Fourier expansion used by bounded-span duality.
Products of character polynomials with centered coefficients at most R
have Fourier support in the corresponding bounded frequency span.
An L1 approximation then forces every sufficiently large Fourier
coefficient into that span. The analytic approximation is a separate input. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Frequencies obtained using coefficients of centered size at most R. -/
def boundedFrequencySpan {N : Nat} {ι : Type*} [Fintype ι] [NeZero N] (gamma : ι → ZMod N) (R : Nat) :
    Finset (ZMod N) :=
  Finset.univ.image fun v : ι → centeredBall N R => ∑ i, (v i : ZMod N) * gamma i

/-- A product of finite character polynomials, with one factor per frequency. -/
def boundedCharacterProduct {N : Nat} {ι : Type*} [Fintype ι] [NeZero N] (gamma : ι → ZMod N) (R : Nat)
    (c : ι → centeredBall N R → Complex) (x : ZMod N) : Complex :=
  ∏ i, ∑ a : centeredBall N R, c i a * exponential ((a : ZMod N) * gamma i * x)

/-- Expand the product; each resulting frequency belongs to the bounded span. -/
theorem boundedCharacterProduct_expansion {N : Nat} {ι : Type*} [Fintype ι] [NeZero N]
    (gamma : ι → ZMod N) (R : Nat) (c : ι → centeredBall N R → Complex)
    (x : ZMod N) :
    boundedCharacterProduct gamma R c x =
      ∑ v : ι → centeredBall N R,
        (∏ i, c i (v i)) * exponential ((∑ i, (v i : ZMod N) * gamma i) * x) := by
  unfold boundedCharacterProduct
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, Finset.sum_mul]
  congr 1
  change (∏ i, (ZMod.stdAddChar (N := N)) ((v i : ZMod N) * gamma i * x)) = _
  have hexp (s : Finset (ι)) :
      (∏ i ∈ s, ZMod.stdAddChar ((v i : ZMod N) * gamma i * x)) =
        ZMod.stdAddChar (∑ i ∈ s, (v i : ZMod N) * gamma i * x) := by
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert i s hi ih => simp [hi, ih, AddChar.map_add_eq_mul]
  exact hexp Finset.univ

/-- Orthogonality makes the Fourier transform vanish outside the span. -/
theorem fourier_boundedCharacterProduct_eq_zero {N : Nat} {ι : Type*} [Fintype ι] [NeZero N]
    (gamma : ι → ZMod N) (R : Nat) (c : ι → centeredBall N R → Complex)
    {xi : ZMod N} (hxi : xi ∉ boundedFrequencySpan gamma R) :
    fourier (boundedCharacterProduct gamma R c) xi = 0 := by
  have hneq (v : ι → centeredBall N R) : (∑ i, (v i : ZMod N) * gamma i) ≠ xi := by
    intro h
    exact hxi (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, h⟩)
  unfold fourier
  rw [ZMod.dft_apply]
  simp only [boundedCharacterProduct_expansion, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  have heq (x : ZMod N) :
      ZMod.stdAddChar (-(x * xi)) *
          ((∏ i, c i (v i)) * exponential ((∑ i, (v i : ZMod N) * gamma i) * x)) =
        (∏ i, c i (v i)) *
          exponential (((∑ i, (v i : ZMod N) * gamma i) - xi) * x) := by
    rw [show ((∑ i, (v i : ZMod N) * gamma i) - xi) * x =
      (∑ i, (v i : ZMod N) * gamma i) * x + -(x * xi) by ring]
    simp only [exponential, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun x _ => heq x, ← Finset.mul_sum]
  have hsum : (∑ x : ZMod N,
      exponential (((∑ i, (v i : ZMod N) * gamma i) - xi) * x)) = 0 := by
    have h := AddChar.sum_mulShift ((∑ i, (v i : ZMod N) * gamma i) - xi)
      (ZMod.isPrimitive_stdAddChar N)
    rw [if_neg (sub_ne_zero.mpr (hneq v))] at h
    simpa only [exponential, mul_comm, Nat.cast_zero] using h
  rw [hsum, mul_zero]

/-- The bounded span has at most (2R+1)^m elements, also when R wraps. -/
theorem boundedFrequencySpan_card_le {N : Nat} {ι : Type*} [Fintype ι] [NeZero N]
    (gamma : ι → ZMod N) (R : Nat) :
    (boundedFrequencySpan gamma R).card ≤ (2 * R + 1)^(Fintype.card ι) := by
  have hball : (centeredBall N R).card ≤ 2 * R + 1 := by
    by_cases hR : 2 * R < N
    · rw [centeredBall_eq_image hR]
      exact Finset.card_image_le.trans (by simp)
    · have h := Finset.card_le_univ (centeredBall N R)
      rw [ZMod.card] at h
      omega
  calc
    (boundedFrequencySpan gamma R).card ≤
        Fintype.card (ι → centeredBall N R) := Finset.card_image_le
    _ = (centeredBall N R).card ^ Fintype.card ι := by simp
    _ ≤ (2 * R + 1)^(Fintype.card ι) := Nat.pow_le_pow_left hball (Fintype.card ι)

/-- L1 approximation by a bounded character product places every large
Fourier coefficient in the bounded frequency span. -/
theorem large_fourier_mem_boundedFrequencySpan {N : Nat} {ι : Type*} [Fintype ι] [NeZero N]
    (gamma : ι → ZMod N) (R : Nat) (c : ι → centeredBall N R → Complex)
    (f : ZMod N → Complex) {epsilon : Real}
    (happrox : (∑ x, ‖f x - boundedCharacterProduct gamma R c x‖) < epsilon * N)
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier f xi‖) :
    xi ∈ boundedFrequencySpan gamma R := by
  by_contra hxi
  have hz := fourier_boundedCharacterProduct_eq_zero gamma R c hxi
  have hdiff : fourier (fun x => f x - boundedCharacterProduct gamma R c x) xi =
      fourier f xi := by
    simp only [fourier, ZMod.dft_apply, smul_sub, Finset.sum_sub_distrib] at hz ⊢
    rw [hz, sub_zero]
  have hnorm : ‖fourier (fun x => f x - boundedCharacterProduct gamma R c x) xi‖ ≤
      ∑ x, ‖f x - boundedCharacterProduct gamma R c x‖ := by
    unfold fourier
    rw [ZMod.dft_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x _
    rw [smul_eq_mul, norm_mul, (ZMod.stdAddChar (N := N)).norm_apply, one_mul]
  rw [hdiff] at hnorm
  linarith

end LeanProofs.GowersSzemeredi
