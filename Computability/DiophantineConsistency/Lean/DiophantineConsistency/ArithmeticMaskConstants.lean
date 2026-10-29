import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ArithmeticWindowDigits
import DiophantineConsistency.ArithmeticMaskData
import DiophantineConsistency.ArithmeticMaskKernel

/-! The fixed standard constants of the current encoding, inside every model of IΣ1.
Facts about the 94517-bit numerals `lowPort`, `highPort` and the kernel `K` are
transferred from ℕ through `Nat.cast` (a semiring hom), never by evaluating the
numerals in the model: digits come from their standard digit lists, populations
from the populations of the 2011 standard digits, and the kernel from its
finite sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticMaskConstants
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticWindowDigits ArithmeticMaskData
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Casts -/

theorem cast_exp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V) := by
  exact ArithmeticStandardCasts.cast_exp n

theorem cast_mod (a b : ℕ) : ((a % b : ℕ) : V) = (a:V) % (b:V) := by
  exact ArithmeticStandardCasts.cast_mod a b

theorem cast_div (a b : ℕ) : ((a / b : ℕ) : V) = (a:V) / (b:V) := by
  exact ArithmeticStandardCasts.cast_div a b

/-- Population of a standard numeral below `2^f` is its fuelled ℕ popcount. -/
theorem cast_population (f n : ℕ) (hn : n < 2^f) : population (n:V) = (pcF f n : V) := by
  induction f generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst this; simp [pcF]
  | succ f ih =>
    have h2 : (2:V) = ((2:ℕ):V) := by simp
    have hn2 : n / 2 < 2^f := by rw [pow_succ] at hn; omega
    rw [population_div_mod, h2, ← cast_div, ← cast_mod, ih (n/2) hn2, pcF,
      Nat.cast_add, add_comm]

/-- Digit extraction from a standard radix-`2^w` digit list. -/
theorem dig_ofDigits (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2^w) (j : ℕ) :
    dig (w:V) ((Nat.ofDigits (2^w) l : ℕ) : V) (j:V) = ((l.getD j 0 : ℕ) : V) := by
  induction l generalizing j with
  | nil => simp [dig]
  | cons a l ih =>
    have ha : (a:V) < Exp.exp (w:V) := by
      rw [cast_exp]; exact_mod_cast hl a (by simp)
    have he : ((Nat.ofDigits (2^w) (a :: l) : ℕ) : V) =
        ((Nat.ofDigits (2^w) l : ℕ) : V) * Exp.exp (w:V) + (a:V) := by
      rw [Nat.ofDigits_cons, cast_exp]; push_cast; ring
    rw [he]
    cases j with
    | zero =>
      rw [Nat.cast_zero, List.getD_cons_zero]
      exact dig_succ_zero _ _ _ ha
    | succ j =>
      rw [Nat.cast_succ, dig_succ_pos _ _ _ _ ha (by simp), add_tsub_cancel_right,
        List.getD_cons_succ]
      exact ih (fun x hx => hl x (by simp [hx])) j

/-- Population of a number given by a standard digit list. -/
theorem population_ofDigits (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2^w) :
    population ((Nat.ofDigits (2^w) l : ℕ) : V) = ((l.map (pcF w)).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : (a:V) < Exp.exp (w:V) := by
      rw [cast_exp]; exact_mod_cast hl a (by simp)
    have he : ((Nat.ofDigits (2^w) (a :: l) : ℕ) : V) =
        ((Nat.ofDigits (2^w) l : ℕ) : V) * Exp.exp (w:V) + (a:V) := by
      rw [Nat.ofDigits_cons, cast_exp]; push_cast; ring
    rw [he, concatenate _ _ _ ha, ih (fun x hx => hl x (by simp [hx])),
      cast_population w a (hl a (by simp)), List.map_cons, List.sum_cons]
    push_cast
    ring

/-- A standard digit list of length `L` gives a number below `2^{wL}`. -/
theorem ofDigits_lt_exp (w : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 2^w) :
    ((Nat.ofDigits (2^w) l : ℕ) : V) < Exp.exp ((w:V) * (l.length : V)) := by
  have hNat : Nat.ofDigits (2^w) l < 2^(w * l.length) := by
    cases w with
    | zero =>
      simp only [pow_zero, Nat.zero_mul, Nat.ofDigits_one] at *
      simp [List.sum_eq_zero (fun x hx => Nat.lt_one_iff.mp (hl x hx))]
    | succ w =>
      rw [pow_mul]
      exact Nat.ofDigits_lt_base_pow_length (by simp) hl
  rw [← Nat.cast_mul, cast_exp]
  exact_mod_cast hNat

/-! ### The masks -/

theorem lowPort_lt_exp : (CurrentMasks2011.lowPort : V) < Exp.exp ((47:V)*2011) := by
  have h := ofDigits_lt_exp (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx)
  rw [lowDigits_length, ← radix_eq, ← lowPort_ofDigits] at h
  simpa using h

theorem highPort_lt_exp : (CurrentMasks2011.highPort : V) < Exp.exp ((47:V)*2011) := by
  have h := ofDigits_lt_exp (V:=V) 47 CurrentMasks2011.highDigits
    (fun x hx => highDigits_lt' hx)
  rw [highDigits_length, ← highPort_ofDigits] at h
  simpa using h

/-- The low support `S = [0,951) ∪ [960,986) ∪ {1004}` as an internal Σ0 predicate. -/
def inS (j : V) : Prop := j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1004

theorem inS_cast (j : ℕ) : inS (j:V) ↔ (j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1004) := by
  unfold inS
  norm_cast

theorem inS_zero : inS (0:V) := Or.inl (by simp)

private theorem low_digit (j : V) (hj : j < 2011) :
    ∃ j₀ : ℕ, j = j₀ ∧ j₀ < 2011 ∧ dig (47:V) (CurrentMasks2011.lowPort:V) j =
      ((lowDigits.getD j₀ 0 : ℕ) : V) := by
  obtain ⟨j₀, rfl⟩ := eq_nat_of_lt_nat (n := 2011) (by simpa using hj)
  have hj₀ : j₀ < 2011 := by exact_mod_cast hj
  refine ⟨j₀, rfl, hj₀, ?_⟩
  have h := dig_ofDigits (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx) j₀
  rw [← radix_eq, ← lowPort_ofDigits] at h
  simpa using h

private theorem cast_radix_sub (b : ℕ) (hb : b ≤ 2^47) :
    ((CurrentMasks2011.radix - b : ℕ) : V) = Exp.exp (47:V) - (b:V) := by
  have h1 : CurrentMasks2011.radix - b + b = CurrentMasks2011.radix :=
    Nat.sub_add_cancel (by rw [radix_eq]; exact hb)
  have h2 : ((CurrentMasks2011.radix - b : ℕ) : V) + (b:V) = (CurrentMasks2011.radix : V) := by
    exact_mod_cast h1
  have h3 : ((CurrentMasks2011.radix : ℕ) : V) = Exp.exp (47:V) := by
    have := cast_exp (V:=V) 47
    rw [Nat.cast_ofNat] at this
    rw [this, radix_eq]
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

theorem lowPort_digit_in (j : V) (hj : j < 2011) (hS : inS j) :
    dig (47:V) (CurrentMasks2011.lowPort:V) j = Exp.exp 47 - 2 := by
  obtain ⟨j₀, rfl, hj₀, h⟩ := low_digit j hj
  rw [h, lowDigits_getD j₀ hj₀, if_pos ((inS_cast j₀).mp hS), cast_radix_sub 2 (by decide)]
  simp

theorem lowPort_digit_out (j : V) (hj : j < 2011) (hS : ¬ inS j) :
    dig (47:V) (CurrentMasks2011.lowPort:V) j = Exp.exp 47 - 1 := by
  obtain ⟨j₀, rfl, hj₀, h⟩ := low_digit j hj
  rw [h, lowDigits_getD j₀ hj₀, if_neg (fun h' => hS ((inS_cast j₀).mpr h')),
    cast_radix_sub 1 (by decide)]
  simp

/-- The high-mask digits are the standard list `highDigits`. -/
theorem highPort_digit (j : ℕ) :
    dig (47:V) (CurrentMasks2011.highPort:V) (j:V) =
      ((CurrentMasks2011.highDigits.getD j 0 : ℕ) : V) := by
  have h := dig_ofDigits (V:=V) 47 CurrentMasks2011.highDigits (fun x hx => highDigits_lt' hx) j
  rw [← highPort_ofDigits] at h
  simpa using h

theorem highPort_digit_zero : dig (47:V) (CurrentMasks2011.highPort:V) 0 = 4 := by
  have h := highPort_digit (V:=V) 0
  rw [highDigits_zero] at h
  simpa using h

theorem ports_population :
    population (CurrentMasks2011.lowPort:V) + population (CurrentMasks2011.highPort:V) =
      94517 := by
  have h1 := population_ofDigits (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx)
  have h2 := population_ofDigits (V:=V) 47 CurrentMasks2011.highDigits
    (fun x hx => highDigits_lt' hx)
  rw [← radix_eq, ← lowPort_ofDigits] at h1
  rw [← highPort_ofDigits] at h2
  rw [h1, h2, ← Nat.cast_add, digit_population]
  simp

theorem lowPort_even : (CurrentMasks2011.lowPort:V) % 2 = 0 := by
  have h0 := lowPort_digit_in (V:=V) 0 (by norm_num) inS_zero
  rw [dig_zero_index] at h0
  have hρ : Exp.exp (47:V) = 2 * Exp.exp 46 := by
    rw [show (47:V) = 46 + 1 by norm_num, exp_succ]
  obtain ⟨e, he⟩ : ∃ e, Exp.exp (46:V) = e + 1 :=
    ⟨Exp.exp 46 - 1, (tsub_add_cancel_of_le (one_le_exp _)).symm⟩
  have hX := div_add_mod (CurrentMasks2011.lowPort:V) (Exp.exp 47)
  rw [h0, hρ, he, show 2*(e+1) - 2 = 2*e by
    rw [show (2:V)*(e+1) = 2*e+2 by ring, add_tsub_cancel_right]] at hX
  rw [← hX, show ∀ Y : V, 2*(e+1)*Y + 2*e = 2*((e+1)*Y + e) from fun Y => by ring]
  exact mod_mul_self_right _ _

theorem highPort_mod_eight : (CurrentMasks2011.highPort:V) % 8 = 4 := by
  have h0 := highPort_digit_zero (V:=V)
  rw [dig_zero_index] at h0
  have h8 : Exp.exp (3:V) = 8 := by
    have := cast_exp (V:=V) 3
    rw [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have hρ : Exp.exp (47:V) = 8 * Exp.exp 44 := by
    rw [show (47:V) = 3 + 44 by norm_num, exp_add, h8]
  have hX := div_add_mod (CurrentMasks2011.highPort:V) (Exp.exp 47)
  rw [h0, hρ] at hX
  rw [← hX, show ∀ Y : V, 8 * Exp.exp 44 * Y + 4 = (Exp.exp 44 * Y) * 8 + 4 from
    fun Y => by ring]
  exact mod_mul_add_of_lt _ _ (by norm_num)

theorem highPort_pos : (0:V) < (CurrentMasks2011.highPort:V) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have h0 := highPort_digit_zero (V:=V)
  rw [h] at h0
  simp [dig] at h0

/-! ### The kernel -/

theorem cast_radix_pow (e : ℕ) :
    ((CurrentMasks2011.radix : ℕ) : V)^e = Exp.exp (47 * (e:V)) := by
  have h : (47:V) * (e:V) = ((47*e : ℕ) : V) := by norm_cast
  rw [h, cast_exp, radix_eq, pow_mul]
  push_cast
  rfl

theorem kernel_sum : (CurrentKernel2011.K : V) =
    ∑ t : CurrentKernel2011.Term,
      (CurrentKernel2011.coefficient t : V) * Exp.exp (47 * (CurrentKernel2011.exponent t : V)) := by
  have hK : CurrentKernel2011.K = ∑ t : CurrentKernel2011.Term,
      CurrentKernel2011.coefficient t * CurrentMasks2011.radix ^ CurrentKernel2011.exponent t := by
    unfold CurrentKernel2011.K CurrentKernel2011.rawWord; rfl
  rw [hK, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Nat.cast_mul, Nat.cast_pow, cast_radix_pow]

theorem kernel_mass :
    ∑ t : CurrentKernel2011.Term, (CurrentKernel2011.coefficient t : V) = 7659829036801887 := by
  rw [← Nat.cast_sum, ArithmeticMaskKernel.coefficient_mass]
  simp

end DiophantineConsistency.ArithmeticMaskConstants
