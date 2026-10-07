import OAI.Combinatorics.Progressions.Lattices.NearIntegerMultiples

namespace OAI

section

namespace Erdos3

def denseProductBudget : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, B => 512*B^2*(denseProductBudget n (16*B^2)+1)

theorem denseProductBudget_pos (n B : ℕ) (hB : 1 ≤ B) : 0 < denseProductBudget n B := by
  have hBp : 0 < B := by omega
  cases n <;> simp only [denseProductBudget] <;> positivity

theorem denseProductBudget_step_bounds (n B : ℕ) (hB : 1 ≤ B) :
    8*B ≤ denseProductBudget (n+1) B ∧
    denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B ∧
    256*B^2 ≤ denseProductBudget (n+1) B ∧
    384*B^2*denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B ∧
    8*B*denseProductBudget n (16*B^2) ≤ denseProductBudget (n+1) B := by
  let C := denseProductBudget n (16*B^2)
  have hC : 1 ≤ C := denseProductBudget_pos n (16*B^2) (by nlinarith)
  have hsq : B ≤ B^2 := by nlinarith
  have hs1 : 1 ≤ B^2 := by nlinarith
  have hBC : B*C ≤ B^2*C := Nat.mul_le_mul_right C hsq
  have hBC' : B ≤ B^2*C := hsq.trans (le_mul_of_one_le_right (Nat.zero_le _) hC)
  have hCC : C ≤ B^2*C := le_mul_of_one_le_left (Nat.zero_le C) hs1
  have hsqC : B^2 ≤ B^2*C := le_mul_of_one_le_right (Nat.zero_le _) hC
  have hlarge : 384*B^2*C ≤ 512*B^2*(C+1) := by nlinarith [Nat.zero_le (B^2*C)]
  change 8*B ≤ 512*B^2*(C+1) ∧ C ≤ 512*B^2*(C+1) ∧
    256*B^2 ≤ 512*B^2*(C+1) ∧ 384*B^2*C ≤ 512*B^2*(C+1) ∧
    8*B*C ≤ 512*B^2*(C+1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  exact ⟨hlarge, by nlinarith⟩

def denseProductExponent : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*denseProductExponent n+2

def denseProductConstant : ℕ → ℕ
  | 0 => 1
  | n+1 => 512*(denseProductConstant n*16^denseProductExponent n+1)

theorem denseProductConstant_pos (n : ℕ) : 0 < denseProductConstant n := by
  cases n <;> simp only [denseProductConstant] <;> positivity

theorem denseProductBudget_le_power (n B : ℕ) (hB : 1 ≤ B) :
    denseProductBudget n B ≤ denseProductConstant n*B^denseProductExponent n := by
  induction n generalizing B with
  | zero => simp [denseProductBudget, denseProductConstant, denseProductExponent]
  | succ n ih =>
    have hB' : 1 ≤ 16*B^2 := by nlinarith
    have hp : 1 ≤ B^(2*denseProductExponent n) := by
      have := pow_pos (show 0 < B by omega) (2*denseProductExponent n)
      omega
    calc
      _ ≤ 512*B^2*(denseProductConstant n*(16*B^2)^denseProductExponent n+1) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (ih (16*B^2) hB') 1)
      _ = 512*B^2*(denseProductConstant n*16^denseProductExponent n*B^(2*denseProductExponent n)+1) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ 512*B^2*(denseProductConstant n*16^denseProductExponent n*B^(2*denseProductExponent n)+
          B^(2*denseProductExponent n)) := by gcongr
      _ = denseProductConstant (n+1)*B^denseProductExponent (n+1) := by
        simp only [denseProductConstant, denseProductExponent, pow_add, pow_two]
        ring

end Erdos3

end

section

namespace Erdos3

def denseProductDensityConstant (e : ℕ) : ℕ :=
  denseProductConstant e * 2^denseProductExponent e

noncomputable def denseProductDensityBudget (e : ℕ) (η : ℝ) : ℝ :=
  (denseProductDensityConstant e : ℝ)/η^denseProductExponent e

theorem denseProductExponent_add_two (e : ℕ) :
    denseProductExponent e + 2 = 2^(e+1) := by
  induction e with
  | zero => norm_num [denseProductExponent]
  | succ e ih =>
    simp only [denseProductExponent, pow_succ] at *
    omega

theorem denseProductDensityBudget_pos (e : ℕ) {η : ℝ} (hη : 0 < η) :
    0 < denseProductDensityBudget e η := by
  have hc : 0 < denseProductConstant e := denseProductConstant_pos e
  unfold denseProductDensityBudget denseProductDensityConstant
  positivity

theorem reciprocal_density_ceil {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ ⌈1/η⌉₊ ∧ 1/(⌈1/η⌉₊ : ℝ) ≤ η ∧ (⌈1/η⌉₊ : ℝ) ≤ 2/η := by
  have hpos : 1 ≤ ⌈1/η⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hceilpos : (0 : ℝ) < ⌈1/η⌉₊ := by exact_mod_cast hpos
  have hle := Nat.le_ceil (1/η)
  have hnear := (Nat.ceil_lt_add_one (show 0 ≤ 1/η by positivity)).le
  refine ⟨hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hceilpos).mpr
    nlinarith [(div_le_iff₀ hη).mp hle]
  · have hone : 1 ≤ 1/η := (le_div_iff₀ hη).mpr (by simpa using hη1)
    calc
      _ ≤ 1/η+1 := hnear
      _ ≤ 1/η+1/η := add_le_add le_rfl hone
      _ = 2/η := by ring

theorem denseProductBudget_ceil_le (e : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (denseProductBudget e ⌈1/η⌉₊ : ℝ) ≤ denseProductDensityBudget e η := by
  obtain ⟨hB, _, hceil⟩ := reciprocal_density_ceil hη hη1
  calc
    (denseProductBudget e ⌈1/η⌉₊ : ℝ) ≤
        (denseProductConstant e : ℝ)*(⌈1/η⌉₊ : ℝ)^denseProductExponent e := by
      exact_mod_cast denseProductBudget_le_power e ⌈1/η⌉₊ hB
    _ ≤ (denseProductConstant e : ℝ)*(2/η)^denseProductExponent e := by gcongr
    _ = denseProductDensityBudget e η := by
      simp only [denseProductDensityBudget, denseProductDensityConstant, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, div_pow]
      ring

end Erdos3

end

end OAI
