import Lean.Elab.Tactic.Omega

/-!
Kernel-checkable arithmetic helpers for a proposed DiophantineConsistency
refactoring.  These are new helper lemmas, not replacements already integrated
into ProveIt.  Checked with Lean 4.32.0 and no Mathlib dependency.
-/

namespace DiophantineConsistency.RefactorPrototype

/-- The exact half-radix shift; unlike finite-case proofs this applies to
arbitrary input digits and any positive scale. -/
theorem halfRadix_exact {s : Nat} (hs : 0 < s) (a b : Nat) :
    (s * a) % (2 * s) + (s * b) / (2 * s) =
      s * (a % 2) + b / 2 := by
  rw [Nat.mul_comm 2 s, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ hs]

/-- The existing digits-at-most-three bound follows from the exact formula. -/
theorem halfRadix_bound {s a b : Nat} (hs : 0 < s) (hb : b ≤ 3) :
    (s * a) % (2 * s) + (s * b) / (2 * s) ≤ s + 1 := by
  rw [halfRadix_exact hs]
  have hm : a % 2 ≤ 1 := by omega
  have hm' := Nat.mul_le_mul_left s hm
  omega

/-- Parity at an even half-radix needs only the predecessor bound. -/
theorem halfRadix_parity {s a b : Nat} (hs : 0 < s) (heven : s % 2 = 0)
    (hb : b ≤ 3) :
    ((s * a) % (2 * s) + (s * b) / (2 * s)) % 2 = b / 2 := by
  rw [halfRadix_exact hs, Nat.add_mod, Nat.mul_mod, heven]
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Dispatch an index to one of q full blocks and a final short block.
Individual block facts may remain separate kernel-checked declarations. -/
theorem forall_lt_by_chunks {P : Nat → Prop} {B q r : Nat} (hB : 0 < B)
    (hblocks : ∀ k, k < q → ∀ j, j < B → P (B * k + j))
    (htail : ∀ j, j < r → P (B * q + j)) :
    ∀ i, i < B * q + r → P i := by
  intro i hi
  by_cases hfull : i < B * q
  · have hk : i / B < q :=
      (Nat.div_lt_iff_lt_mul hB).mpr (by simpa only [Nat.mul_comm] using hfull)
    have h := hblocks (i / B) hk (i % B) (Nat.mod_lt i hB)
    simpa only [Nat.div_add_mod] using h
  · have h := htail (i - B * q) (by omega)
    simpa only [Nat.add_sub_of_le (by omega : B * q ≤ i)] using h

/-- With a bounded remainder, exact local decomposition already determines
the quotient.  A normalization record need not store both facts. -/
theorem quotient_of_decomposition {radix total digit carry : Nat}
    (hdigit : digit < radix) (hlocal : total = digit + radix * carry) :
    carry = total / radix := by
  rw [hlocal, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hdigit,
    Nat.zero_add]

/-- The remainder is likewise determined by the same decomposition. -/
theorem remainder_of_decomposition {radix total digit carry : Nat}
    (hdigit : digit < radix) (hlocal : total = digit + radix * carry) :
    digit = total % radix := by
  rw [hlocal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdigit]

/-- A proof certificate for an existing carry assignment.  Construction of
this certificate must still be proved from the actual equation. -/
structure CarryCertificate {I : Type} (radix budget : Nat)
    (raw : I → Nat) (prev : I → I) (carry digits : I → Nat) : Prop where
  carry_le : ∀ i, carry i ≤ budget
  digit_lt : ∀ i, digits i < radix
  decompose : ∀ i, raw i + carry (prev i) = digits i + radix * carry i

theorem CarryCertificate.recurrence {I : Type} {radix budget : Nat}
    {raw : I → Nat} {prev : I → I} {carry digits : I → Nat}
    (h : CarryCertificate radix budget raw prev carry digits) (i : I) :
    carry i = (raw i + carry (prev i)) / radix :=
  quotient_of_decomposition (h.digit_lt i) (h.decompose i)

#print axioms halfRadix_exact
#print axioms halfRadix_bound
#print axioms halfRadix_parity
#print axioms forall_lt_by_chunks
#print axioms quotient_of_decomposition
#print axioms remainder_of_decomposition
#print axioms CarryCertificate.recurrence

end DiophantineConsistency.RefactorPrototype
