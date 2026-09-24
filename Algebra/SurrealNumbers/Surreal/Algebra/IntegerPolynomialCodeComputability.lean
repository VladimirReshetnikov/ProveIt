import Surreal.Algebra.IntegerPolynomialCode
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursive validity of integer polynomial coefficient codes

The finite signed coefficient representation in `odg:def:thm:saturation`.
This proves primitive recursiveness using Mathlib's natural-number encodings;
it is distinct from the executable recognizer on native formula syntax.
-/

namespace Surreal.IntegerPolynomialCode

/-- Reading a coefficient from a finite list, defaulting to zero, is primitive recursive. -/
theorem coefficient_primrec : Primrec₂ coefficient :=
  (Primrec.option_getD.comp₂ Primrec.list_getElem? (Primrec.const 0))

/-- Nonempty coefficient lists with nonzero last coefficient form a primitive-recursive set. -/
theorem canonical_primrec : PrimrecPred Canonical := by
  apply PrimrecPred.and
  · exact Primrec.nat_lt.comp (Primrec.const 0) Primrec.list_length
  · exact (Primrec.eq.comp
      (coefficient_primrec.comp Primrec.id
        (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))) (Primrec.const 0)).not

/-- The validity-checking Boolean function is primitive recursive, not just classically decidable. -/
theorem canonical_decide_primrec : Primrec (fun l : List ℤ => decide (Canonical l)) :=
  canonical_primrec.decide

end Surreal.IntegerPolynomialCode
