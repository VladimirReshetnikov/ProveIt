import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic.Ring

/-! A quotient/remainder uniqueness argument valid over nonstandard
model naturals. No external well-foundedness or standard-Nat representation
is assumed. The caller supplies the already established discrete-order law. -/
namespace FreshSimplifications

variable {R : Type*} [CommSemiring R] [LinearOrder R]
  [IsOrderedCancelAddMonoid R]

/-- Multiplication monotonicity at the one comparison actually needed,
obtained from one additive gap rather than a global ordered-ring instance. -/
theorem division_interval_separation
    (hle : ∀ a b : R, a ≤ b ↔ ∃ c, a + c = b)
    {q q' r r' d s : R} (hq : q' = q + s + 1) (hr : r < d) :
    q * d + r < q' * d + r' := by
  have hmul : q * d + d ≤ q' * d :=
    (hle _ _).mpr ⟨s * d, by rw [hq]; ring⟩
  have hfirst : q * d + r < q * d + d := by
    simpa only [add_comm] using add_lt_add_left hr (q * d)
  exact hfirst.trans_le (hmul.trans ((hle _ _).mpr ⟨r', rfl⟩))

/-- The interval argument proves uniqueness in every such model. -/
theorem division_unique_of_discrete_order
    (hle : ∀ a b : R, a ≤ b ↔ ∃ c, a + c = b)
    (hlt : ∀ a b : R, a < b ↔ ∃ c, b = a + c + 1)
    {q r q' r' n d : R} (he : n = q*d+r) (hr : r < d)
    (he' : n = q'*d+r') (hr' : r' < d) : q = q' ∧ r = r' := by
  have not_lt {a b u v : R} (ha : n = a*d+u) (hu : u < d)
      (hb : n = b*d+v) : ¬ a < b := by
    rintro hab
    obtain ⟨s, hs⟩ := (hlt _ _).mp hab
    exact (ne_of_lt (division_interval_separation hle hs hu)) (ha.symm.trans hb)
  have hq : q = q' := le_antisymm (le_of_not_gt (not_lt he' hr' he))
    (le_of_not_gt (not_lt he hr he'))
  subst q'
  exact ⟨rfl, add_left_cancel (he.symm.trans he')⟩

/-- The concrete ObjectDivision proof skeleton, with its existing instances. -/
theorem quotient_not_lt_schema [CanonicallyOrderedAdd R]
    (hle : ∀ a b : R, a ≤ b ↔ ∃ c, a + c = b)
    (hlt : ∀ a b : R, a < b ↔ ∃ c, b = a + c + 1)
    {q r q' r' n d : R} (he : n = q*d+r) (hr : r < d)
    (he' : n = q'*d+r') : ¬ q < q' := by
  intro hq
  obtain ⟨s,hs⟩ := (hlt q q').mp hq
  have hmul : q*d+d ≤ q'*d := (hle _ _).mpr ⟨s*d,by rw [hs]; ring⟩
  have hfirst : q*d+r < q*d+d := by
    simpa only [add_comm] using add_lt_add_left hr (q*d)
  exact (ne_of_lt (hfirst.trans_le (hmul.trans le_self_add))) (he.symm.trans he')

omit [IsOrderedCancelAddMonoid R] in
/-- Once the earlier ordered-semiring and discrete-successor proposals are
assumed applied, even the quotient-gap witness disappears. -/
theorem quotient_not_lt_ordered [IsStrictOrderedRing R] [CanonicallyOrderedAdd R]
    (hdiscrete : ∀ a b : R, a < b → a + 1 ≤ b)
    {q r q' r' n d : R} (hd : 0 ≤ d) (he : n = q*d+r) (hr : r < d)
    (he' : n = q'*d+r') : ¬ q < q' := by
  intro hq
  have hmul := mul_le_mul_of_nonneg_right (hdiscrete q q' hq) hd
  rw [add_mul, one_mul] at hmul
  have hfirst : q*d+r < q*d+d := by
    simpa only [add_comm] using add_lt_add_left hr (q*d)
  exact (ne_of_lt (hfirst.trans_le (hmul.trans le_self_add))) (he.symm.trans he')

#print axioms division_interval_separation
#print axioms division_unique_of_discrete_order
#print axioms quotient_not_lt_schema
#print axioms quotient_not_lt_ordered
end FreshSimplifications
