import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-! Uncompiled standalone ordered-ring consequences; no model bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Sign33OrderedRing

section OrderedRing
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The transport window and `R<E` force the first two cut signs. -/
theorem gap_tau_signs (q F alpha E N k r : R)
    (hq : 1≤q) (halpha : 0≤alpha) (hgap : F+alpha≤q)
    (hE : 0≤E) (hN : 1≤N) (hk : 0≤k) (hr : r≤E) :
    0≤(q-1)*(q-F)+alpha ∧ 0≤E*N+k-r := by
  have ha : 0≤q-F := by linarith
  have hb : 0≤(q-1)*(q-F) := mul_nonneg (sub_nonneg.mpr hq) ha
  have hc : 0≤E*(N-1) := mul_nonneg hE (sub_nonneg.mpr hN)
  constructor <;> nlinarith

/-- Bounds derived from the first-index and strong norms force the next two
cut signs. The discrete step `f≥2` is supplied by the natural-model lemma. -/
theorem inner_V_signs (c T r f : R)
    (hc : 0<c) (hT : 1≤T) (hhalf : 2*r<c) (hf : 2≤f) :
    0≤c*T-r ∧ 0≤f*f*(c*T-r)-c := by
  have hct : 0≤c*(T-1) := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hT)
  have hu : 0<c*T-r := by nlinarith
  have htwo : 0<2*(c*T-r)-c := by nlinarith
  have hf2 : 4≤f*f := by nlinarith [sq_nonneg (f-2)]
  have hprod : 0≤(f*f-4)*(c*T-r) := mul_nonneg (sub_nonneg.mpr hf2) (le_of_lt hu)
  constructor <;> nlinarith

/-- The auxiliary unit norm forces its squared-ordinate difference nonpositive. -/
theorem auxiliary_difference_sign (S V y : R)
    (hS : 0<S) (hy : 1≤y)
    (haux : S*S*(V*V-y*y)+y*y=1) : V*V-y*y≤0 := by
  have hy2 : 1≤y*y := by nlinarith [sq_nonneg (y-1)]
  by_contra h
  have hd : 0<V*V-y*y := lt_of_not_ge h
  have hp : 0<S*S*(V*V-y*y) := mul_pos (mul_pos hS hS) hd
  linarith
end OrderedRing

end Sign33OrderedRing
#print axioms Sign33OrderedRing.gap_tau_signs
#print axioms Sign33OrderedRing.inner_V_signs
#print axioms Sign33OrderedRing.auxiliary_difference_sign
