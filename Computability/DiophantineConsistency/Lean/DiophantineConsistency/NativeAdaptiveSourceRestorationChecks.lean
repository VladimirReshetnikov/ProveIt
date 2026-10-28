import DiophantineConsistency.NativeAdaptiveSourceRestoration

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveSourceRestorationChecks
open NativeAdaptiveSourceRestoration

-- The quotient and the original source transport coordinate differ by one.
example : ∃ z : ℤ, 0<z ∧ 24=8*z ∧ 21=(8-1)*z :=
  transport_quotient (by norm_num) (by norm_num) (by norm_num)

example (J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V : ℤ) :
    source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V 3=z+1 := rfl

example (J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V : ℤ) :
    source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V 28=
      i*((eta+zeta)*Y+eta)^2 := rfl

example {a c D X gamma : ℤ} (ha : 0<a) (hX : 0<X) (hXc : X<c)
    (hD : 0<D) (hn : D^2=1+((a+2)^2-1)*c^2)
    (he : D=X+a*c+(4*a+3)*gamma) : 0<gamma :=
  main_gamma_positive ha ⟨hX,hXc⟩ hD hn he

-- Positivity cannot be removed from the quotient interface.
example : (8:ℤ)*(-21)=(8-1)*(-24) ∧ ¬∃z : ℤ, 0<z ∧ (-24)=8*z := by
  constructor
  · norm_num
  · rintro ⟨z,hz,he⟩
    omega

-- Literal row 12 records exactly the same rank c*j-V, before natural casts.
example (J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V : ℤ) :
    source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V 19*j-
      source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V 26=
      ((eta+zeta)*Y+eta)*j-V := rfl

#print axioms transport_quotient
#print axioms main_gamma_positive
#print axioms source_positive
#print axioms source_rows
#print axioms adaptive_positive_source

end DiophantineConsistency.NativeAdaptiveSourceRestorationChecks
