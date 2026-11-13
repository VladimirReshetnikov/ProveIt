import DiophantineConsistency.Ordinary12FreeJ
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJDescentStep

/-- The adjacent-coefficient Pell transform preserves the norm over every
commutative ring; no inequalities or quotient assumptions are used. -/
theorem transform_preserves_norm {R : Type*} [CommRing R] (q v y : R) :
    let v' := (2*q-1)*v-2*(q-1)*y
    let y' := (2*q-1)*y-2*q*v
    q*v'*v'-(q-1)*y'*y' = q*v*v-(q-1)*y*y := by
  dsimp only
  ring

/-- If b divides q−1 through the *given* witness s, the transformed cleared
numerator differs from a by a multiple of b. No reducedness is assumed. -/
theorem cleared_numerator_step {R : Type*} [CommRing R] (q v a b s : R)
    (h : q-1=b*s) :
    let a' := (2*q-1)*a-2*q*v*b
    a'-a = b*(2*s*a-2*q*v) := by
  dsimp only
  calc
    (2*q-1)*a-2*q*v*b-a = 2*(q-1)*a-2*q*v*b := by ring
    _ = b*(2*s*a-2*q*v) := by rw [h]; ring


/-- A supplied nonzero denominator and Bezout certificate persist after the
cleared transformation. This does not show such a certificate exists. -/
theorem conditional_denominator_invariant {R : Type*} [CommRing R]
    (q v a b s : R) (hb : b ≠ 0) (h : q-1=b*s)
    (hcop : ∃ x y : R, a*x+b*y=1) :
    b ≠ 0 ∧ ∃ x y : R, ((2*q-1)*a-2*q*v*b)*x+b*y=1 := by
  obtain ⟨x,y,hxy⟩ := hcop
  let z := 2*s*a-2*q*v
  have he : ((2*q-1)*a-2*q*v*b)-a=b*z := cleared_numerator_step q v a b s h
  have he' : ((2*q-1)*a-2*q*v*b)-b*z=a := by
    calc
      ((2*q-1)*a-2*q*v*b)-b*z = a+(((2*q-1)*a-2*q*v*b)-a)-b*z := by ring
      _ = a := by rw [he]; ring
  refine ⟨hb,x,y-z*x,?_⟩
  calc
    ((2*q-1)*a-2*q*v*b)*x+b*(y-z*x) =
        (((2*q-1)*a-2*q*v*b)-b*z)*x+b*y := by ring
    _ = 1 := by rw [he']; exact hxy

end FreeJDescentStep
#print axioms FreeJDescentStep.transform_preserves_norm
#print axioms FreeJDescentStep.cleared_numerator_step
#print axioms FreeJDescentStep.conditional_denominator_invariant
