import Surreal.Algebra.IntegerArithmeticComputability
import Surreal.Algebra.RingTermFoldComputability
import Surreal.Algebra.IntegerPolynomialParser

/-!
# Primitive-recursive coefficient extraction from native terms

The coefficient-parser step in `odg:def:thm:saturation`. One structural fold
computes the three existing parser functions together; its projections are
proved equal to the original definitions, including on malformed candidates.
-/

namespace Surreal.IntegerPolynomialParser
open FirstOrder FirstOrder.Language

/-- Integer value, proposed monomial coefficient and proposed coefficient list. -/
abbrev Analysis := ℤ × ℤ × List ℤ

/-- All information needed by the coefficient parser, computed in a single structural fold. -/
def analyze : Language.ring.Term ℕ → Analysis :=
  RingTermFold.fold (fun _ => (0, 0, [])) (0, 0, []) (1, 0, [])
    (fun a => (-a.1, 0, []))
    (fun a b => (a.1 + b.1, 0, a.2.2 ++ [b.2.1]))
    (fun a b => (a.1 * b.1, a.1, []))

/-- The combined fold computes exactly the existing parser on every native term. -/
theorem analyze_eq (t : Language.ring.Term ℕ) :
    analyze t = (integerValue t, monomialCoefficient t, readCoefficients t) := by
  induction t with
  | var n => rfl
  | func f ts ih =>
    simp only [analyze] at ih ⊢
    cases f <;> simp [RingTermFold.fold, ih, integerValue, monomialCoefficient, readCoefficients]

local instance : Primcodable (Language.ring.Term ℕ) := RingTermCode.termPrimcodable

/-- The combined native-term analysis is primitive recursive. -/
theorem analyze_primrec : Primrec analyze := by
  apply RingTermFold.fold_primrec (d := (0, 0, []))
  · exact Primrec.const _
  · exact (IntegerArithmeticComputability.neg_primrec.comp Primrec.fst).pair
      ((Primrec.const 0).pair (Primrec.const []))
  · exact ((IntegerArithmeticComputability.add_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.const 0).pair
        (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.const []))))).to₂
  · exact ((IntegerArithmeticComputability.mul_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.const []))).to₂

/-- The parser's integer-valued term evaluation is primitive recursive. -/
theorem integerValue_primrec : Primrec (integerValue (α := ℕ)) :=
  (Primrec.fst.comp analyze_primrec).of_eq (fun t => by simp [analyze_eq])

/-- Reading the coefficient position of a monomial candidate is primitive recursive. -/
theorem monomialCoefficient_primrec : Primrec (monomialCoefficient (α := ℕ)) :=
  ((Primrec.fst.comp Primrec.snd).comp analyze_primrec).of_eq (fun t => by simp [analyze_eq])

/-- Reading a proposed coefficient list from arbitrary native term syntax is primitive recursive. -/
theorem readCoefficients_primrec : Primrec (readCoefficients (α := ℕ)) :=
  ((Primrec.snd.comp Primrec.snd).comp analyze_primrec).of_eq (fun t => by simp [analyze_eq])

end Surreal.IntegerPolynomialParser
