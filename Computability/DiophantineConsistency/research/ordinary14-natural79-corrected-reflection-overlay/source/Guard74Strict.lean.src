import DiophantineConsistency.DiscreteOrderedRingFacts

/-! Source-only ordered-ring guard fact. All graph-derived inequalities and
its guard balance are explicit hypotheses; no graph zero is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Guard74StrictDraft
open DiscreteOrderedRingFacts
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A shifted positive guard quotient is strictly greater than one. -/
theorem shifted_guard_gt_one (hd : Discrete R) (F alpha X K q b h : R)
    (hF : 0<F) (halpha : 0<alpha) (hX : 0<X) (hK : 0≤K)
    (hXq : q≤X) (hh : 1≤h)
    (hguard : (q-F-alpha)*(X+K)-F=b*(h-1)) : 1<h := by
  by_contra hn
  have he : h=1 := le_antisymm (not_lt.mp hn) hh
  rw [he,sub_self,mul_zero,sub_eq_zero] at hguard
  have hXK : 0<X+K := by linarith
  have hprod : 0<(q-F-alpha)*(X+K) := by rw [hguard]; exact hF
  have hC : 0<q-F-alpha := pos_of_mul_pos_left hprod (le_of_lt hXK)
  have hC1 : 1≤q-F-alpha := hd _ hC
  have hFX : F<X := by linarith
  have hdom : X+K≤(q-F-alpha)*(X+K) := by
    have hm := mul_nonneg (sub_nonneg.mpr hC1) (le_of_lt hXK)
    nlinarith
  have : F<(q-F-alpha)*(X+K) := by linarith
  linarith

end DiophantineConsistency.Guard74StrictDraft

#print axioms DiophantineConsistency.Guard74StrictDraft.shifted_guard_gt_one
