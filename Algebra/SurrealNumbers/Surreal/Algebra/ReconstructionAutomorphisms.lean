import Surreal.Algebra.IdealReconstruction

/-!
# Invariance of reconstruction formulas under ring automorphisms

The algebraic formula-invariance step of `odg:def:thm:autreal`.
Surjectivity is used for the universal multiplier quantifier.
-/

namespace Surreal.IdealReconstruction

variable {R S : Type*} [CommRing R] [CommRing S]

theorem Inf.map (f : R →+* S) {x : R} (hx : Inf x) : Inf (f x) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨f y, ?_⟩
  simpa only [map_pow, map_mul, map_ofNat] using congrArg f hy

theorem inf_equiv (e : R ≃+* S) (x : R) : Inf (e x) ↔ Inf x :=
  ⟨fun h => by
    have hi : Inf (e.symm (e x)) := h.map e.symm.toRingHom
    simpa only [RingEquiv.symm_apply_apply] using hi,
    fun h => h.map e.toRingHom⟩

/-- Universal multiplier witnesses transport using the inverse map on the tested input. -/
theorem Mult.map (e : R ≃+* S) {a b : R} (h : Mult a b) : Mult (e a) (e b) := by
  refine ⟨(map_ne_zero_iff e e.injective).mpr h.1, fun x hx => ?_⟩
  have hx' : Inf (e.symm x) := hx.map e.symm.toRingHom
  obtain ⟨y, hy, he⟩ := h.2 (e.symm x) hx'
  refine ⟨e y, hy.map e.toRingHom, ?_⟩
  simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg e he

theorem mult_equiv (e : R ≃+* S) (a b : R) : Mult (e a) (e b) ↔ Mult a b :=
  ⟨fun h => by simpa only [RingEquiv.symm_apply_apply] using h.map e.symm, fun h => h.map e⟩

/-- The entire coefficient predicate is invariant, including its zero branch. -/
theorem coeff_equiv (e : R ≃+* S) (a b : R) : Coeff (e a) (e b) ↔ Coeff a b := by
  simp only [Coeff, ne_eq, map_eq_zero_iff e e.injective, mult_equiv]

end Surreal.IdealReconstruction
