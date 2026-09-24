import Surreal.Algebra.AlgebraicTypeCode
import Mathlib.Computability.RE

/-!
# Computability of the explicit algebraic omitted type

The computability clause of `odg:def:thm:saturation`. The exact original set
of native parameter-free formulas has primitive-recursive membership under
the explicit prefix coding. This is a ComputablePred theorem, not merely
an executable Boolean function or a classical decidability instance.
-/

namespace Surreal.AlgebraicTypeCode
open FirstOrder FirstOrder.Language
open IntegerPolynomialFormulas IntegerPolynomialCode
local instance : DecidableEq RingFormulaCode.Token := inferInstance
local instance : Primcodable (Language.ring.Term ℕ) := RingTermCode.termPrimcodable

/-- Extracting an equation token's proposed left term is primitive recursive. -/
theorem leftTermCode_primrec : Primrec leftTermCode := by
  have h : Primrec (fun t : RingFormulaCode.Token =>
      (Sum.casesOn t (fun a => a.2.1) (fun _ => []) : List RingTermCode.Token)) :=
    Primrec.sumCasesOn Primrec.id (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to₂
      (Primrec.const []).to₂
  exact h.of_eq (fun t => by cases t <;> rfl)

/-- Coefficient proposals are primitive recursive on arbitrary formula-code streams. -/
theorem candidate_primrec : Primrec candidate := by
  have ht := RingTermCode.decode_primrec.comp (leftTermCode_primrec.comp
    ((Primrec.list_getD (Sum.inr (Sum.inl 0) : RingFormulaCode.Token)).comp Primrec.id (Primrec.const 1)))
  exact Primrec.option_getD.comp
    (Primrec.option_map ht (IntegerPolynomialParser.readCoefficients_primrec.comp Primrec.snd).to₂)
    (Primrec.const [])

/-- Generating the complete canonical inequality code is primitive recursive. -/
theorem inequality_primrec : Primrec inequality := by
  have ht := codeTerm_encode_primrec.comp Primrec.id (Primrec.const (Term.var (0 : ℕ)))
  have ha : Primrec (fun l : List ℤ =>
      (Sum.inl (0, RingTermCode.encode (term l (Term.var 0)), [Sum.inr (0 : Fin 5)]) :
        RingFormulaCode.Token)) :=
    Primrec.sumInl.comp ((Primrec.const 0).pair (ht.pair (Primrec.const ([.inr 0] : List RingTermCode.Token))))
  exact Primrec.list_cons.comp (Primrec.const (.inr (.inr 0) : RingFormulaCode.Token))
    (Primrec.list_cons.comp ha (Primrec.list_cons.comp (Primrec.const (.inr (.inl 0) : RingFormulaCode.Token)) (Primrec.const [])))

/-- Canonical inequality-code membership is primitive recursive. -/
theorem checkNonvanishing_primrec : Primrec checkNonvanishing :=
  ((canonical_primrec.comp candidate_primrec).and
    (Primrec.eq.comp Primrec.id (inequality_primrec.comp candidate_primrec))).decide

/-- Adding any fixed native guard preserves primitive-recursive membership on codes. -/
theorem checkType_primrec (δ : Language.ring.Formula (Fin 1)) : Primrec (checkType δ) :=
  Primrec.or.comp (Primrec.eq.decide.comp Primrec.id (Primrec.const (RingFormulaCode.encode δ)))
    checkNonvanishing_primrec

local instance : Primcodable (Language.ring.Formula (Fin 1)) := RingFormulaCode.fixedFormulaPrimcodable 0

/-- The original native omitted type has primitive-recursive membership. -/
theorem membership_primrec (δ : Language.ring.Formula (Fin 1)) :
    PrimrecPred (fun φ => φ ∈ AlgebraicOmittedType.formulas δ) :=
  (Primrec.eq.comp ((checkType_primrec δ).comp (RingFormulaCode.fixed_encode_primrec 0))
    (Primrec.const true)).of_eq (checkType_encode_iff δ)

/-- The source's native parameter-free type is computable in Mathlib's formal sense. -/
theorem membership_computable (δ : Language.ring.Formula (Fin 1)) :
    ComputablePred (fun φ => φ ∈ AlgebraicOmittedType.formulas δ) :=
  (membership_primrec δ).computablePred

/-- The previously verified native Boolean recognizer is itself primitive recursive. -/
theorem native_checkType_primrec (δ : Language.ring.Formula (Fin 1)) :
    Primrec (IntegerPolynomialParser.checkType δ) := by
  letI := IntegerPolynomialParser.membershipDecidable δ
  exact (membership_primrec δ).decide.of_eq (fun φ => by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, IntegerPolynomialParser.checkType_iff])

end Surreal.AlgebraicTypeCode
