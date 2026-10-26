import DiophantineConsistency.CurrentCount2011
import DiophantineConsistency.CurrentEarlyPadding2011
import DiophantineConsistency.CurrentPhaseParity2011
import DiophantineConsistency.CurrentPolynomialWindow2011

/-!
# Every actual current zero has at most one selector per cell and phase zero

The middle-phase padding premises are derived from the literal kernel and
masks. The preliminary count then applies in every phase, after which the
actual origin-marker parity excludes all fractional phases. Whole-field
alignment, occupation and machine semantics are not assumed or concluded.
-/

namespace DiophantineConsistency.CurrentOneHot2011

open CurrentMasks2011 NativeCyclicConvolution NativeCyclicRotation
  NativeBooleanRotation CurrentClause2011 CurrentCount2011
open scoped BigOperators

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

omit [NeZero (N * 2011)] in
theorem middle_rotation_bound (W : ℕ) (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ i, c i ≤ 1) (hphase : W % 47 ≤ 10) (i : ZMod (N * 2011)) :
    binaryRotation 47 W c i ≤ 2 ^ 10 := by
  rw [rotation_eq_scaled (by decide : 0 < 47) W c hc i]
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hphase
  have hm := Nat.mul_le_mul_left (2 ^ (W % 47)) (hc (i - ((W / 47 : ℕ) : ZMod (N * 2011))))
  omega

omit [NeZero (N * 2011)] in
theorem middle_rotation_mod (W : ℕ) (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ i, c i ≤ 1) (hphase : 7 ≤ W % 47) (i : ZMod (N * 2011)) :
    binaryRotation 47 W c i % 16 = 0 := by
  rw [rotation_eq_scaled (by decide : 0 < 47) W c hc i,
    show W % 47 = 4 + (W % 47 - 4) by omega, pow_add]
  simp only [Nat.mul_mod, show (2 ^ 4 : ℕ) % 16 = 0 from by decide,
    Nat.zero_mul, Nat.zero_mod]

/-- All middle-phase padding information follows from the actual word data. -/
theorem literal_count_le_one (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ i, c i ≤ 1)
    (hsupport : ∀ i, i.val % 2011 ∉ lowSupport → c i = 0)
    (hk : ∀ i, carry i ≤ 57)
    (hlocal : ∀ i, convolution CurrentKernel2011.folded c i + binaryRotation 47 W c i +
      carry (i - 1) = digits i + radix * carry i)
    (hmask : ∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) : selectorCount c b ≤ 1 := by
  apply count_le_one_of_middle_padding c carry digits W hc hsupport hk hlocal hmask b hb
  intro hphase hsmall
  refine ⟨CurrentEarlyPadding2011.paddingUnit c b, ?_⟩
  exact CurrentEarlyPadding2011.padding_bindings c (binaryRotation 47 W c) carry digits
    hc (middle_rotation_bound W c hc hsmall) (middle_rotation_mod W c hc hphase)
    hsupport hk hlocal hmask b hb

theorem physical_count_le_one (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ i, c i ≤ 1)
    (hsupport : ∀ i, i.val % 2011 ∉ lowSupport → c i = 0)
    (hk : ∀ i, carry i ≤ 57)
    (hlocal : ∀ i, convolution CurrentKernel2011.folded c i + binaryRotation 47 W c i +
      carry (i - 1) = digits i + radix * carry i)
    (hmask : ∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1 := by
  have hh := literal_count_le_one c carry digits W hc hsupport hk hlocal hmask b hb
  rw [selectorCount_eq_prefix, PaddingStaircase.prefixSum] at hh
  rw [Fin.sum_univ_eq_sum_range (fun f : ℕ => c (b + (f : ZMod (N * 2011)))) 942]
  exact hh

/-- The original polynomial's data require no additional padding, count or
phase premise. Empty cells are still permitted at this stage. -/
theorem facts_count_phase (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (h : CurrentPolynomialWindow2011.Facts v N x c carry digits) :
    (∀ b : ZMod (N * 2011), b.val % 2011 = 0 →
      (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) ∧
    ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)) % 47 = 0 := by
  have hone := physical_count_le_one c carry digits _ h.boolean h.support h.carry_bound
    h.carry_equation h.mask_tests
  refine ⟨hone, ?_⟩
  have ho := hone 0 (by simp)
  simp only [zero_add] at ho
  exact CurrentPhaseParity2011.fractional_phase_zero _ c carry digits
    h.boolean h.support h.origin h.carry_bound h.carry_recurrence
    h.carry_equation h.mask_tests ho

def CountPhaseWindow (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ x : Fin 31 → ℕ, ∃ c carry digits : ZMod (N * 2011) → ℕ,
    CurrentPolynomialWindow2011.Facts v N x c carry digits ∧
    (∀ b : ZMod (N * 2011), b.val % 2011 = 0 →
      (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) ∧
    ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)) % 47 = 0

theorem polynomial_zero_count_phase (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v CurrentPolynomialWindow2011.polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, CountPhaseWindow v N hN := by
  obtain ⟨N, hN, hwin⟩ := CurrentPolynomialWindow2011.polynomial_zero_window v hv hz
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x, c, carry, digits, h⟩ := hwin
  exact ⟨N, hN, x, c, carry, digits, h, facts_count_phase v x c carry digits h⟩

end DiophantineConsistency.CurrentOneHot2011
