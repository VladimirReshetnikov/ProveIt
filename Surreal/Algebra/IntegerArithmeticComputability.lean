import Surreal.Algebra.IntegerPolynomialTermComputability

/-!
# Primitive-recursive integer arithmetic for the syntax recognizer

The coefficient-evaluation step of `odg:def:thm:saturation`. The standard
Mathlib signed-integer encoding is retained. Integer operations are reduced
to natural arithmetic on positive and negative parts.
-/

namespace Surreal.IntegerArithmeticComputability

/-- The nonnegative integer constructor is primitive recursive. -/
theorem ofNat_primrec : Primrec Int.ofNat :=
  Primrec.encode_iff.mp ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun _ => rfl))

/-- The negative-successor integer constructor is primitive recursive. -/
theorem negSucc_primrec : Primrec Int.negSucc :=
  Primrec.encode_iff.mp ((Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun _ => rfl))

/-- The difference of two naturals, computed in the standard signed representation. -/
def difference (a b : ℕ) : ℤ := if b ≤ a then .ofNat (a - b) else .negSucc (b - a - 1)

/-- The computational signed difference has the expected integer value. -/
theorem difference_eq (a b : ℕ) : difference a b = (a : ℤ) - (b : ℤ) := by
  unfold difference
  split
  · rename_i h
    change ((a - b : ℕ) : ℤ) = (a : ℤ) - b
    exact Int.natCast_sub h
  · omega

/-- Signed subtraction of natural inputs is primitive recursive. -/
theorem difference_primrec : Primrec₂ difference :=
  (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (ofNat_primrec.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (negSucc_primrec.comp (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))).to₂

/-- Taking the positive part of an integer is primitive recursive. -/
theorem toNat_primrec : Primrec Int.toNat := by
  have h : Primrec (fun z : ℤ => (Sum.casesOn (Equiv.intEquivNatSumNat z) id (fun _ => 0) : ℕ)) :=
    Primrec.sumCasesOn IntegerPolynomialFormulas.signMagnitude_primrec
      Primrec.snd.to₂ (Primrec.const 0).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

/-- Taking the magnitude of the negative part is primitive recursive. -/
theorem negativePart_primrec : Primrec (fun z : ℤ => (-z).toNat) := by
  have h : Primrec (fun z : ℤ =>
      (Sum.casesOn (Equiv.intEquivNatSumNat z) (fun _ => 0) Nat.succ : ℕ)) :=
    Primrec.sumCasesOn IntegerPolynomialFormulas.signMagnitude_primrec
      (Primrec.const 0).to₂ (Primrec.succ.comp Primrec.snd).to₂
  exact h.of_eq (fun z => by
    cases z with
    | ofNat n => change 0 = (-(n : ℤ)).toNat; simp
    | negSucc n => rfl)

/-- Integer negation is primitive recursive under Mathlib's standard integer encoding. -/
theorem neg_primrec : Primrec (fun z : ℤ => -z) :=
  (difference_primrec.comp negativePart_primrec toNat_primrec).of_eq (fun z => by
    rw [difference_eq]
    have h := Int.toNat_sub_toNat_neg z
    omega)

/-- Integer addition is primitive recursive. -/
theorem add_primrec : Primrec₂ (fun a b : ℤ => a + b) := by
  have h := difference_primrec.comp
    (Primrec.nat_add.comp (toNat_primrec.comp Primrec.fst) (toNat_primrec.comp Primrec.snd))
    (Primrec.nat_add.comp (negativePart_primrec.comp Primrec.fst) (negativePart_primrec.comp Primrec.snd))
  exact h.to₂.of_eq (fun a b => by
    rw [difference_eq]
    push_cast
    have ha := Int.toNat_sub_toNat_neg a
    have hb := Int.toNat_sub_toNat_neg b
    omega)

/-- Integer multiplication is primitive recursive. -/
theorem mul_primrec : Primrec₂ (fun a b : ℤ => a * b) := by
  have h := difference_primrec.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (toNat_primrec.comp Primrec.fst) (toNat_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativePart_primrec.comp Primrec.fst) (negativePart_primrec.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (toNat_primrec.comp Primrec.fst) (negativePart_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativePart_primrec.comp Primrec.fst) (toNat_primrec.comp Primrec.snd)))
  exact h.to₂.of_eq (fun a b => by
    rw [difference_eq]
    push_cast
    calc
      _ = ((a.toNat : ℤ) - (-a).toNat) * ((b.toNat : ℤ) - (-b).toNat) := by ring
      _ = a * b := by rw [Int.toNat_sub_toNat_neg, Int.toNat_sub_toNat_neg])

end Surreal.IntegerArithmeticComputability
