import OAI.Combinatorics.Progressions.Lattices.IntegerRadixCoding
import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boxCodeModulus {n : ℕ} (T : Fin n → ℕ) : ℕ := ∏ i, 4 * T i

def boxIntegerCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ :=
  integerRadixHom (fun i => 4 * T i)

def boxCyclicCode {n : ℕ} (T : Fin n → ℕ) : (Fin n → ℤ) →+ ZMod (boxCodeModulus T) :=
  (Int.castAddHom (ZMod (boxCodeModulus T))).comp (boxIntegerCode T)

theorem boxCodeModulus_pos {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    0 < boxCodeModulus T :=
  Finset.prod_pos (fun i _ => Nat.mul_pos (by norm_num) (NeZero.pos (T i)))

instance boxCodeModulus_neZero {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    NeZero (boxCodeModulus T) := ⟨(boxCodeModulus_pos T).ne'⟩

theorem boxCodeModulus_eq {n : ℕ} (T : Fin n → ℕ) :
    boxCodeModulus T = 4 ^ n * ∏ i, T i := by
  simp [boxCodeModulus, Finset.prod_mul_distrib]

theorem boxIntegerCode_bounds {n : ℕ} (T : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : x ∈ integerBox T) :
    0 ≤ boxIntegerCode T x ∧ boxIntegerCode T x < (boxCodeModulus T : ℤ) := by
  apply integerRadixValue_bounds
  intro i
  have h := (mem_integerBox T x).mp hx i
  constructor
  · exact h.1
  · push_cast
    omega

theorem boxCyclicCode_reflectsPairSums {n : ℕ} (T : Fin n → ℕ) :
    ReflectsPairSums (boxCyclicCode T) (integerBox T : Set (Fin n → ℤ)) := by
  intro a ha b hb c hc d hd he
  have hab : ∀ i, 0 ≤ (a + b) i ∧ (a + b) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T a).mp ha i
    have h2 := (mem_integerBox T b).mp hb i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have hcd : ∀ i, 0 ≤ (c + d) i ∧ (c + d) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T c).mp hc i
    have h2 := (mem_integerBox T d).mp hd i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have he' : ((boxIntegerCode T (a + b) : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T (c + d) : ℤ) : ZMod (boxCodeModulus T)) := by
    change ((boxIntegerCode T a : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T b : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T c : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T d : ℤ) : ZMod (boxCodeModulus T)) at he
    simpa only [map_add, Int.cast_add] using he
  have hh := int_eq_of_zmod_eq_of_bounds
    (integerRadixValue_bounds (fun i => 4 * T i) (a + b) hab)
    (integerRadixValue_bounds (fun i => 4 * T i) (c + d) hcd) he'
  exact integerRadixValue_injective_on_digits (fun i => 4 * T i) (a + b) (c + d) hab hcd hh

theorem boxCyclicCode_injOn {n : ℕ} (T : Fin n → ℕ) :
    Set.InjOn (boxCyclicCode T) (integerBox T : Set (Fin n → ℤ)) :=
  (boxCyclicCode_reflectsPairSums T).injOn

theorem boxCyclicCode_representative {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)]
    (x : Fin n → ℤ) (hx : x ∈ integerBox T) :
    ((boxCyclicCode T x).val : ℤ) = boxIntegerCode T x := by
  change (((boxIntegerCode T x : ℤ) : ZMod (boxCodeModulus T)).val : ℤ) = _
  rw [ZMod.val_intCast]
  exact Int.emod_eq_of_lt (boxIntegerCode_bounds T x hx).1 (boxIntegerCode_bounds T x hx).2

theorem boxCode_density {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) = ((4 : ℝ) ^ n)⁻¹ := by
  have hprod : ((∏ i, T i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (T i)))
  rw [card_integerBox, boxCodeModulus_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hprod]

theorem boxCode_density_lower {n : ℕ} (T : Fin n → ℕ) [∀ i, NeZero (T i)] :
    Real.exp (-(4 * (n : ℝ))) ≤ ((integerBox T).card : ℝ) / (boxCodeModulus T : ℝ) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpow : (4 : ℝ) ^ n ≤ Real.exp (4 * (n : ℝ)) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 n
    rw [← Real.exp_nat_mul] at h
    simpa only [mul_comm] using h
  rw [boxCode_density, ← one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mpr
  calc
    _ ≤ Real.exp (-(4 * (n : ℝ))) * Real.exp (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3

end

end OAI
