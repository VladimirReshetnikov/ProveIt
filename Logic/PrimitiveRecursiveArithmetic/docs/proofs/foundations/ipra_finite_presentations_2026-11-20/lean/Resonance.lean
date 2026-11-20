import Std

/-! Finite coefficient kernel, over rational real parameters for the executable
    examples. The paper uses pairs of rationals to cover complex parameters. -/
namespace Resonance

def partialSum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | j + 1 => partialSum f j + f j

def poch (x : Rat) : Nat → Rat
  | 0 => 1
  | j+1 => poch x j * (x + j)

def fac : Nat → Nat
  | 0 => 1
  | j+1 => fac j * (j+1)

def gauss (a b : Rat) (m : Nat) : Nat → Rat
  | 0 => 1
  | j+1 =>
    gauss a b m j * (a+j) * (b+j) / (((j+1 : Nat) : Rat) * (m+j+1 : Nat))

def binSeries (q : Rat) : Nat → Rat
  | 0 => 1
  | j+1 => binSeries q j * ((j : Rat)-q) / (j+1 : Nat)

/-- Increasing prefix array, constant coefficient stored at index zero. -/
def inversePrefix (u : Nat → Rat) : Nat → Array Rat
  | 0 => #[1]
  | j+1 =>
    let old := inversePrefix u j
    let entry := -partialSum (fun i => u (i+1) * old[j-i]?.getD 0) (j+1)
    old.push entry

def conv (u v : Nat → Rat) (j : Nat) : Rat :=
  partialSum (fun i => u i * v (j-i)) (j+1)

def obstruction (a b : Rat) (m : Nat) : Rat :=
  let inv := inversePrefix (gauss a b m) m
  let w := fun j => inv[j]?.getD 0
  conv (binSeries ((m : Rat)-a-b)) (conv w w) m

def productObstruction (a b : Rat) (m : Nat) : Rat :=
  (-1 : Rat)^m * poch (a-m) m * poch (b-m) m / (fac m : Rat)^2

theorem inversePrefix_size (u : Nat → Rat) (n : Nat) :
    (inversePrefix u n).size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [inversePrefix, ih]

theorem obstruction_zero (a b : Rat) : obstruction a b 0 = 1 := by
  simp [obstruction, inversePrefix, conv, partialSum, binSeries]
  decide +kernel

example : obstruction (1/2) (1/2) 2 = 9/64 := by decide +kernel
example : productObstruction (1/2) (1/2) 2 = 9/64 := by decide +kernel
example : obstruction 1 (5/3) 3 = 0 := by decide +kernel
example : productObstruction 1 (5/3) 3 = 0 := by decide +kernel

/-! A pure integer precision bound. Clearing the final analytic tail estimate
    leaves cap * 2^p ≤ 2^(p+cap); no logarithm routine is required. -/
theorem le_dyadic (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 0 < 2^n := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

theorem truncation_budget (cap p : Nat) : cap * 2^p ≤ 2^(p+cap) := by
  rw [Nat.pow_add, Nat.mul_comm cap]
  exact Nat.mul_le_mul_left _ (le_dyadic cap)


/-- A bounded zero criterion for a Pochhammer symbol. -/
theorem poch_zero_iff (x : Rat) (m : Nat) :
    poch x m = 0 ↔ ∃ i : Nat, i < m ∧ x+i = 0 := by
  induction m with
  | zero =>
    constructor
    · intro h
      have h10 : (1 : Rat) ≠ 0 := by decide +kernel
      exact False.elim (h10 h)
    · rintro ⟨i, hi, _⟩
      omega
  | succ m ih =>
    rw [poch, Rat.mul_eq_zero, ih]
    constructor
    · rintro (⟨i, hi, he⟩ | he)
      · exact ⟨i, by omega, he⟩
      · exact ⟨m, by omega, he⟩
    · rintro ⟨i, hi, he⟩
      by_cases e : i = m
      · exact Or.inr (e ▸ he)
      · exact Or.inl ⟨i, by omega, he⟩

private theorem rat_pow_ne_zero (v : Rat) (hv : v ≠ 0) (m : Nat) : v^m ≠ 0 := by
  induction m with
  | zero =>
    rw [Rat.pow_zero]
    decide +kernel
  | succ m ih =>
    rw [Rat.pow_succ]
    intro h
    exact (Rat.mul_eq_zero.mp h).elim ih hv

private theorem fac_nonzero (m : Nat) : fac m ≠ 0 := by
  induction m with
  | zero => decide
  | succ m ih => simp [fac, Nat.mul_eq_zero, ih]

/-- The zero set of the closed obstruction is decided by two bounded searches. -/
theorem product_zero_iff (a b : Rat) (m : Nat) :
    productObstruction a b m = 0 ↔
     (∃ i : Nat, i < m ∧ (a-m)+i = 0) ∨ (∃ i : Nat, i < m ∧ (b-m)+i = 0) := by
  have hden : (fac m : Rat)^2 ≠ 0 :=
    rat_pow_ne_zero _ (fun h => fac_nonzero m (Rat.natCast_eq_zero_iff.mp h)) 2
  have hsign : (-1 : Rat)^m ≠ 0 := rat_pow_ne_zero _ (by decide +kernel) m
  unfold productObstruction
  constructor
  · intro h
    have hp := congrArg (· * (fac m : Rat)^2) h
    rw [Rat.div_mul_cancel hden, Rat.zero_mul, Rat.mul_eq_zero, Rat.mul_eq_zero] at hp
    rcases hp with ((hz | hz) | hz)
    · exact False.elim (hsign hz)
    · exact Or.inl ((poch_zero_iff _ _).mp hz)
    · exact Or.inr ((poch_zero_iff _ _).mp hz)
  · rintro (ha | hb)
    · rw [(poch_zero_iff _ _).mpr ha, Rat.mul_zero, Rat.zero_mul, Rat.div_def, Rat.zero_mul]
    · rw [(poch_zero_iff _ _).mpr hb, Rat.mul_zero, Rat.div_def, Rat.zero_mul]

end Resonance

#print axioms Resonance.product_zero_iff
#print axioms Resonance.truncation_budget
