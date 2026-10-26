import PolynomialZeroTransport

namespace DiophantineConsistency.PolynomialZeroTransportClients
variable {σ R : Type*}

/-- Literal selection residual in ObjectConditional.literal_selection,
with variable indices left abstract to cover its actual Sum slots. -/
def selectionRow (out bit zero positive : σ) : Expr σ :=
  .sub (.var out) (.add (.mul (.var bit) (.var zero))
    (.mul (.sub (.constant 1) (.var bit)) (.var positive)))

def normalizedSelectionRow (out bit zero positive : σ) : Expr σ :=
  .sub (.add (.var out) (.mul (.var bit) (.var positive)))
    (.add (.mul (.var bit) (.var zero)) (.var positive))

theorem selection_polynomial_identity (out bit zero positive : σ) :
    (selectionRow out bit zero positive).toPolynomial =
      (normalizedSelectionRow out bit zero positive).toPolynomial := by
  simp only [selectionRow, normalizedSelectionRow, Expr.toPolynomial]
  simp only [map_one]
  ring

/-- The actual object-layer equation, established over arbitrary cancellative
semirings by an integer-polynomial identity and the generic transfer theorem. -/
theorem selection_zero_iff [CommSemiring R] [IsCancelAdd R]
    (out bit zero positive : σ) (v : σ → R) :
    ((selectionRow out bit zero positive).splitNatural.1.evalSemiring v =
      (selectionRow out bit zero positive).splitNatural.2.evalSemiring v) ↔
    v out + v bit * v positive = v bit * v zero + v positive := by
  refine (Expr.splitNatural_zero_iff_of_polynomial_eq _ _
    (selection_polynomial_identity out bit zero positive) v).trans ?_
  simp [normalizedSelectionRow, Expr.splitNatural, NatExpr.evalSemiring]

/-- Instantiate the same input slots used by ObjectConditional. -/
example [CommSemiring R] [IsCancelAdd R] (x : Fin 6 → R) :
    ((selectionRow (Sum.inl (0 : Fin 6)) (Sum.inl 4) (Sum.inl 2) (Sum.inl 3)).splitNatural.1.evalSemiring
      (Sum.elim x (Fin.elim0 : Fin 0 → R)) =
    (selectionRow (Sum.inl (0 : Fin 6)) (Sum.inl 4) (Sum.inl 2) (Sum.inl 3)).splitNatural.2.evalSemiring
      (Sum.elim x (Fin.elim0 : Fin 0 → R))) ↔
      x 0 + x 4 * x 3 = x 4 * x 2 + x 3 :=
  selection_zero_iff _ _ _ _ _

#print axioms selection_polynomial_identity
#print axioms selection_zero_iff
end DiophantineConsistency.PolynomialZeroTransportClients

namespace CancellationNegativeControl
open DiophantineConsistency

local instance : Zero Bool := ⟨false⟩
local instance : One Bool := ⟨true⟩
local instance : Add Bool := ⟨Bool.or⟩
local instance : Mul Bool := ⟨Bool.and⟩

/-- Boolean OR/AND semiring. Its addition is not cancellative. -/
local instance booleanSemiring : CommSemiring Bool where
  zero := false
  one := true
  add := Bool.or
  mul := Bool.and
  nsmul := nsmulRec
  npow := npowRec
  natCast := fun n => n != 0
  zero_add := by decide
  add_zero := by decide
  add_assoc := by decide
  add_comm := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  natCast_zero := rfl
  natCast_succ n := by cases n <;> rfl

def e : Expr (Fin 0) := .constant 1
def f : Expr (Fin 0) := .sub (.constant 2) (.constant 1)

theorem same_integer_polynomial : e.toPolynomial = f.toPolynomial := by
  simp [e, f, Expr.toPolynomial]
  ring

theorem first_not_zero :
    ¬ (e.splitNatural.1.evalSemiring (Fin.elim0 : Fin 0 → Bool) =
      e.splitNatural.2.evalSemiring Fin.elim0) := by decide

theorem second_zero :
    f.splitNatural.1.evalSemiring (Fin.elim0 : Fin 0 → Bool) =
      f.splitNatural.2.evalSemiring Fin.elim0 := by decide

#print axioms same_integer_polynomial
#print axioms first_not_zero
#print axioms second_zero
end CancellationNegativeControl
