import DiophantineConsistency.ArithmeticGcdNormalization

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticGcdNormalizationChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Total unique fixed syntax, including both inputs zero. -/
example (a b : V) : ∃! g : V, gcdDef.val.Evalb ![g,a,b] := gcd_total a b

example (b : V) : gcdValue 0 b=b := by
  apply Eq.symm
  apply (gcd_graph 0 b b).mp
  refine ⟨dvd_zero b,dvd_refl b,0,0,0,1,?_⟩
  simp

example (a : V) : gcdValue a 0=a := by
  apply Eq.symm
  apply (gcd_graph a 0 a).mp
  refine ⟨dvd_refl a,dvd_zero a,0,0,1,0,?_⟩
  simp

/-- Greatestness includes a zero common divisor; no positivity is hidden. -/
example (a b h : V) (ha : h∣a) (hb : h∣b) : h∣gcdValue a b :=
  bez_divisor (gcd_spec a b).2.2 ha hb

/-- Coprime cancellation is a consequence of the actual coefficient identity. -/
example (t d x u v w z : V)
    (hu : 1+t*u+d*v=t*w+d*z) (hx : d∣t*x) : d∣x :=
  unit_certificate_cancel ⟨u,v,w,z,hu⟩ hx

/-- The actual first relaxed-norm shape uses no supplied gcd or index. -/
example (R D f : V) (hR : 0<R) (hD : 0<D) (hf : 0<f)
    (hn : R*R=D*(f*f-1)) :
    ∃ d s t : V, 0<d ∧ 0<s ∧ 0<t ∧
      D=d*d*s ∧ R=d*s*t ∧ f*f=1+s*t*t :=
  norm_normalization_tsub R D f hR hD hf hn

#print axioms gcd_certificate_exists
#print axioms gcd_certificate_unique
#print axioms gcd_certificate_total
#print axioms gcd_defined
#print axioms gcd_total
#print axioms unit_certificate_cancel
#print axioms norm_normalization
#print axioms norm_normalization_tsub
end DiophantineConsistency.ArithmeticGcdNormalizationChecks
