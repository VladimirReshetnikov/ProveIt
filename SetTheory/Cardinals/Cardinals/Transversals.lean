/-
  NO FINITE-VALUED TRANSVERSAL, FOR THE ACTUAL EMBEDDING (synthesis Theorem 9.10 and
  Corollary 12.5, for sets fixed by `j`).

  Consequences of `RelWitness.zero_or_full`: a set `T ∈ X` of countable cofinal subsets of
  `λ` with `j(T) = T` cannot meet an orbit class in a nonempty finite set; in particular
  it is not a transversal, and not a finite-valued multisection, at any orbit class.

  Nothing is admitted in this file.
-/
import Cardinals.Orbits

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

/-- The trace of `T` on the class of the orbit of `r`. -/
noncomputable def trace (T : ZFSet.{u}) (r : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun b => EvAgreeZ (ordZ c.ord) b (w.orb r)) T

/-- **No nonempty small trace**: a fixed `T` meets an orbit class in `0` or at least `λ`
points; so every trace of size below `λ` -- in particular every finite trace -- is empty. -/
theorem trace_eq_empty_of_card_lt (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) (hU : w.IsUltra)
    (T : Str w.X Y) (hT : w.jv T = T.1)
    (hTmem : ∀ b ∈ T.1, CofinalIn b c.ord ∧ ZFSet.card b ≤ ℵ₀)
    {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord)
    (hsmall : ZFSet.card (w.trace T.1 r) < c) : w.trace T.1 r = ∅ := by
  rcases w.zero_or_full (w.aleph0_lt hc) hα hU T hT hTmem hκ hr with h | h
  · exact h
  · exact absurd hsmall (not_lt.mpr h)

/-- **No fixed transversal (synthesis Theorem 9.10):** a fixed `T` does not meet an orbit
class in exactly one point. -/
theorem no_fixed_transversal (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) (hU : w.IsUltra)
    (T : Str w.X Y) (hT : w.jv T = T.1)
    (hTmem : ∀ b ∈ T.1, CofinalIn b c.ord ∧ ZFSet.card b ≤ ℵ₀)
    {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord) (b : ZFSet.{u}) :
    w.trace T.1 r ≠ {b} := by
  intro hb
  have hc' := w.aleph0_lt hc
  have hsmall : ZFSet.card (w.trace T.1 r) < c := by
    rw [hb, ZFSet.card_singleton]
    exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hc
  have := w.trace_eq_empty_of_card_lt hc hα hU T hT hTmem hκ hr hsmall
  rw [hb] at this
  have hmem : b ∈ ({b} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [this] at hmem
  exact ZFSet.notMem_empty b hmem

end RelWitness

end Cardinals
