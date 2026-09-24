import Surreal.Algebra.RingTermCodeComputability
import Surreal.Algebra.IntegerPolynomialCodeComputability

/-!
# Primitive-recursive generation of native integer polynomial terms

The forward syntax-coding step in `odg:def:thm:saturation`. Under the explicit
prefix coding of native terms, signed numerals, powers and finite coefficient
sums are primitive recursive. No noncomputable polynomial representation is
used as input to these algorithms.
-/

namespace Surreal.IntegerPolynomialFormulas
open FirstOrder FirstOrder.Language
open RingTermCode

local instance : Primcodable (Language.ring.Term ℕ) := termPrimcodable

/-- Unary natural numerals are primitive recursive in native term syntax. -/
theorem numeral_primrec : Primrec (ArithmeticGuards.numeral (α := ℕ)) := by
  have h := Primrec.nat_rec₁ (0 : Language.ring.Term ℕ)
    (add_primrec.comp Primrec.snd (Primrec.const 1)).to₂
  exact h.of_eq (fun n => by induction n <;> simp [ArithmeticGuards.numeral, *])

/-- The standard integer encoding makes the sign/magnitude split primitive recursive. -/
theorem signMagnitude_primrec : Primrec Equiv.intEquivNatSumNat := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.of_eq (fun z : ℤ => by cases z <;> rfl)

/-- Signed integer numerals are primitive recursive, including negative successors. -/
theorem integerNumeral_primrec : Primrec (integerNumeral (α := ℕ)) := by
  have h := Primrec.sumCasesOn signMagnitude_primrec
    (numeral_primrec.comp Primrec.snd).to₂
    (neg_primrec.comp (numeral_primrec.comp (Primrec.succ.comp Primrec.snd))).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

/-- Native powers are primitive recursive in the base term and exponent. -/
theorem power_primrec : Primrec₂ (power (α := ℕ)) := by
  have h := Primrec.nat_rec (Primrec.const (1 : Language.ring.Term ℕ))
    (mul_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  exact h.of_eq (fun t n => by induction n <;> simp [power, *])

/-- The finite coefficient sum is primitive recursive in list, variable term and cutoff. -/
theorem partialSum_coefficients_primrec :
    Primrec₂ (fun (p : List ℤ × Language.ring.Term ℕ) n =>
      partialSum (IntegerPolynomialCode.coefficient p.1) p.2 n) := by
  have h := Primrec.nat_rec (Primrec.const (0 : Language.ring.Term ℕ))
    (add_primrec.comp (Primrec.snd.comp Primrec.snd)
      (mul_primrec.comp
        (integerNumeral_primrec.comp (IntegerPolynomialCode.coefficient_primrec.comp
          (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
        (power_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))).to₂
  exact h.of_eq (fun p n => by induction n <;> simp [partialSum, *])

/-- Building a polynomial term from its finite coefficient code is primitive recursive. -/
theorem codeTerm_primrec : Primrec₂ (IntegerPolynomialCode.term (α := ℕ)) :=
  partialSum_coefficients_primrec.comp Primrec.id (Primrec.list_length.comp Primrec.fst)

/-- The generated term's finite token code is itself primitive recursive. -/
theorem codeTerm_encode_primrec :
    Primrec₂ (fun (l : List ℤ) (t : Language.ring.Term ℕ) =>
      RingTermCode.encode (IntegerPolynomialCode.term l t)) :=
  (encode_primrec.comp codeTerm_primrec).to₂

end Surreal.IntegerPolynomialFormulas
