import Init

/-!
Core-only independent check of the concrete multiplicative periods.
This does not import or validate the Mathlib adapter order_eq_of_factors.
The evaluator reduces modulo m after every multiplication; its equality
with the ordinary natural power modulo m is proved below.
-/
namespace ProofSimplification20261026

def residuePower (b m : Nat) : Nat → Nat
  | 0 => 1 % m
  | n + 1 => (residuePower b m n * b) % m

theorem residuePower_eq (b m n : Nat) : residuePower b m n = b ^ n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residuePower, ih, Nat.pow_succ]
    exact Nat.mod_mul_mod _ _ _

/-- A closed certificate for a finite candidate return time. -/
def finiteReturn (b m n : Nat) : Prop :=
  0 < n ∧ residuePower b m n = 1 ∧
    ∀ k : Fin n, k.val ≠ 0 → residuePower b m k.val ≠ 1

/-- The ordinary mathematical first-positive-return statement. -/
def LeastPositiveReturn (b m n : Nat) : Prop :=
  0 < n ∧ b ^ n % m = 1 ∧
    ∀ k : Nat, 0 < k → k < n → b ^ k % m ≠ 1

theorem finiteReturn_sound {b m n : Nat} (h : finiteReturn b m n) :
    LeastPositiveReturn b m n := by
  refine ⟨h.1, ?_, ?_⟩
  · simpa only [residuePower_eq] using h.2.1
  · intro k hk hkn
    have he := h.2.2 ⟨k, hkn⟩ (Nat.ne_of_gt hk)
    simpa only [residuePower_eq] using he

theorem certificate47 : finiteReturn 2 47 23 := by unfold finiteReturn; decide +kernel

theorem certificate2011 : finiteReturn 2 2011 402 := by unfold finiteReturn; decide +kernel

theorem leastReturn47 : LeastPositiveReturn 2 47 23 := finiteReturn_sound certificate47

theorem leastReturn2011 : LeastPositiveReturn 2 2011 402 := finiteReturn_sound certificate2011

/-- The proper-power residues used by the smaller prime-factor certificate. -/
theorem properResidues2011 :
    residuePower 2 2011 201 = 2010 ∧
    residuePower 2 2011 134 = 205 ∧ residuePower 2 2011 6 = 64 := by decide +kernel

/-- A candidate proper divisor really is rejected. -/
example : ¬ finiteReturn 2 2011 201 := by unfold finiteReturn; decide +kernel

/-- n=1 is permitted and needs no positive smaller-exponent test. -/
example : finiteReturn 1 7 1 := by unfold finiteReturn; decide +kernel

/-- Zero must not be accepted as a positive order certificate. -/
example : ¬ finiteReturn 1 7 0 := by unfold finiteReturn; decide +kernel

#print axioms residuePower_eq
#print axioms finiteReturn_sound
#print axioms certificate47
#print axioms certificate2011
#print axioms leastReturn47
#print axioms leastReturn2011
#print axioms properResidues2011

end ProofSimplification20261026
