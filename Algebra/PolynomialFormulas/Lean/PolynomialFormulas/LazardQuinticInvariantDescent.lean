import PolynomialFormulas.LazardQuinticInvariantSystem
import PolynomialFormulas.QuinticScalarGaloisBridge

/-!
# Descent of Lazard's root invariants

When the Figure-3 matrix is nonsingular, its four linear equations make
`i₅,…,i₈` unique once `i₄` is fixed.  Consequently a rational `i₄` forces
the complete root-origin invariant tuple to be Galois-fixed and hence
rational.  This removes four independent rationality certificates.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open QuinticScalarGaloisBridge

set_option autoImplicit false

section Fixed

variable {K : Type*} [Field K] [CharZero K]

/-- Reflection counterpart of `InvariantRelations.map`. -/
theorem InvariantRelations.of_map
    {L : Type*} [Field L] [CharZero L]
    {c : DepressedQuintic K} {i : Invariants K} (φ : K →+* L)
    (hφ : Function.Injective φ)
    (h : InvariantRelations (c.map φ) (i.map φ)) :
    InvariantRelations c i := by
  constructor
  · apply hφ
    simpa [resolventEval, resolventCore, discriminant, DepressedQuintic.map,
      Invariants.map, map_ofNat] using h.resolvent
  · apply hφ
    simpa [i4SquareRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      h.square
  · apply hφ
    simpa [i4CubeRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      h.cube
  · apply hφ
    simpa [i4FourthRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      h.fourth
  · apply hφ
    simpa [i4FifthRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      h.fifth

/-- Uniqueness of Figure 3 propagates invariance of `i₄` to the complete
invariant tuple. -/
theorem InvariantRelations.map_eq_self_of_i4_fixed
    {c : DepressedQuintic K} {i : Invariants K}
    (h : InvariantRelations c i) (hdet : (invariantSystemMatrix c).det ≠ 0)
    (σ : K →+* K) (hc : c.map σ = c) (
      hi4 : σ i.i4 = i.i4) :
    i.map σ = i := by
  have hmap := h.map σ
  rw [hc] at hmap
  exact hmap.eq_of_i4_eq_of_det_ne_zero h
    (by simpa [Invariants.map] using hi4) hdet

end Fixed

section Rational

/-- A root-origin invariant tuple descends from the splitting field to
`Q` once `i₄` is rational and the Figure-3 matrix is nonsingular. -/
theorem exists_rational_invariants_of_i4_rational
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (i : Invariants c.polynomial.SplittingField)
    (h : InvariantRelations
      (c.map (algebraMap ℚ c.polynomial.SplittingField)) i)
    (hdet : (invariantSystemMatrix
      (c.map (algebraMap ℚ c.polynomial.SplittingField))).det ≠ 0)
    (hi4 : ∃ q : ℚ, algebraMap ℚ c.polynomial.SplittingField q = i.i4) :
    ∃ j : Invariants ℚ,
      InvariantRelations c j ∧
        j.map (algebraMap ℚ c.polynomial.SplittingField) = i := by
  obtain ⟨q4, hq4⟩ := hi4
  have hcoeff (σ : c.polynomial.Gal) :
      (c.map (algebraMap ℚ c.polynomial.SplittingField)).map σ.toRingHom =
        c.map (algebraMap ℚ c.polynomial.SplittingField) := by
    cases c
    simp [DepressedQuintic.map]
  have hi4fixed (σ : c.polynomial.Gal) : σ i.i4 = i.i4 := by
    rw [← hq4]
    exact σ.commutes q4
  have hfixed (σ : c.polynomial.Gal) : i.map σ.toRingHom = i :=
    h.map_eq_self_of_i4_fixed hdet σ.toRingHom (hcoeff σ) (hi4fixed σ)
  have hcoord (coord : Invariants c.polynomial.SplittingField →
      c.polynomial.SplittingField)
      (hmap : ∀ (j : Invariants c.polynomial.SplittingField)
        (σ : c.polynomial.Gal), coord (j.map σ.toRingHom) = σ (coord j)) :
      coord i ∈ Set.range (algebraMap ℚ c.polynomial.SplittingField) := by
    rw [mem_range_algebraMap_iff_gal_fixed c.polynomial hp]
    intro σ
    rw [← hmap i σ, hfixed σ]
  have hi5 := hcoord Invariants.i5 (by intro j σ; rfl)
  have hi6 := hcoord Invariants.i6 (by intro j σ; rfl)
  have hi7 := hcoord Invariants.i7 (by intro j σ; rfl)
  have hi8 := hcoord Invariants.i8 (by intro j σ; rfl)
  obtain ⟨q5, hq5⟩ := hi5
  obtain ⟨q6, hq6⟩ := hi6
  obtain ⟨q7, hq7⟩ := hi7
  obtain ⟨q8, hq8⟩ := hi8
  let j : Invariants ℚ := ⟨q4, q5, q6, q7, q8⟩
  have hj : j.map (algebraMap ℚ c.polynomial.SplittingField) = i := by
    cases i
    simp only [j, Invariants.map] at hq4 hq5 hq6 hq7 hq8 ⊢
    simp_all
  refine ⟨j, ?_, hj⟩
  apply InvariantRelations.of_map
    (algebraMap ℚ c.polynomial.SplittingField)
    (algebraMap ℚ c.polynomial.SplittingField).injective
  simpa [hj] using h

end Rational

end LeanProofs.PolynomialFormulas.LazardQuintic
