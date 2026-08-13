import PolynomialFormulas.LazardQuinticInvariantSystem

/-!
# Scalar transport for Lazard's invariant system

The Figure-3 matrix and its determinant commute with extension of scalars.
These elementary transport facts are shared by the printed root-origin path
and the denominator-safe coefficient-descent path, so they are kept below
both constructions.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

section Transport

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]

private theorem i4SquareRhs_map
    (c : DepressedQuintic K) (i : Invariants K) (phi : K →+* L) :
    i4SquareRhs (c.map phi) (i.map phi) = phi (i4SquareRhs c i) := by
  simp [i4SquareRhs, DepressedQuintic.map, Invariants.map, map_ofNat]

private theorem i4CubeRhs_map
    (c : DepressedQuintic K) (i : Invariants K) (phi : K →+* L) :
    i4CubeRhs (c.map phi) (i.map phi) = phi (i4CubeRhs c i) := by
  simp [i4CubeRhs, DepressedQuintic.map, Invariants.map, map_ofNat]

private theorem i4FourthRhs_map
    (c : DepressedQuintic K) (i : Invariants K) (phi : K →+* L) :
    i4FourthRhs (c.map phi) (i.map phi) = phi (i4FourthRhs c i) := by
  simp [i4FourthRhs, DepressedQuintic.map, Invariants.map, map_ofNat]

private theorem i4FifthRhs_map
    (c : DepressedQuintic K) (i : Invariants K) (phi : K →+* L) :
    i4FifthRhs (c.map phi) (i.map phi) = phi (i4FifthRhs c i) := by
  simp [i4FifthRhs, DepressedQuintic.map, Invariants.map, map_ofNat]

private theorem invariantSystemRhs_map_apply
    (c : DepressedQuintic K) (i : Invariants K) (phi : K →+* L)
    (row : Fin 4) :
    invariantSystemRhs (c.map phi) (i.map phi) row =
      phi (invariantSystemRhs c i row) := by
  fin_cases row <;>
    simp [invariantSystemRhs, i4SquareRhs_map, i4CubeRhs_map,
      i4FourthRhs_map, i4FifthRhs_map]

private theorem invariantSystemLinear_map_apply
    (c : DepressedQuintic K) (tail : Fin 4 → K) (phi : K →+* L)
    (row : Fin 4) :
    invariantSystemLinear (c.map phi) (fun col ↦ phi (tail col)) row =
      phi (invariantSystemLinear c tail row) := by
  have htail :
      Invariants.ofI4Tail (0 : L) (fun col ↦ phi (tail col)) =
        (Invariants.ofI4Tail (0 : K) tail).map phi := by
    simp [Invariants.ofI4Tail, Invariants.map]
  have hzero :
      Invariants.ofI4Tail (0 : L) (0 : Fin 4 → L) =
        (Invariants.ofI4Tail (0 : K) (0 : Fin 4 → K)).map phi := by
    simp [Invariants.ofI4Tail, Invariants.map]
  simp only [invariantSystemLinear, Pi.sub_apply, htail, hzero,
    invariantSystemRhs_map_apply, map_sub]

/-- The Figure-3 coefficient matrix commutes with extension of scalars. -/
theorem invariantSystemMatrix_map (c : DepressedQuintic K) (phi : K →+* L) :
    invariantSystemMatrix (c.map phi) =
      phi.mapMatrix (invariantSystemMatrix c) := by
  ext row col
  change invariantSystemLinear (c.map phi)
      (Pi.single col (1 : L) : Fin 4 → L) row =
    phi (invariantSystemLinear c
      (Pi.single col (1 : K) : Fin 4 → K) row)
  have hsingle :
      (Pi.single col (1 : L) : Fin 4 → L) =
        fun j : Fin 4 ↦
          phi ((Pi.single col (1 : K) : Fin 4 → K) j) := by
    funext j
    by_cases h : col = j <;> simp [h]
  rw [hsingle]
  exact invariantSystemLinear_map_apply c
    (Pi.single col (1 : K) : Fin 4 → K) phi row

/-- Nonsingularity of the Figure-3 system is preserved by extension of
scalars. -/
theorem invariantSystemMatrix_det_ne_zero_map
    (c : DepressedQuintic K) (phi : K →+* L)
    (hdet : (invariantSystemMatrix c).det ≠ 0) :
    (invariantSystemMatrix (c.map phi)).det ≠ 0 := by
  rw [invariantSystemMatrix_map, ← phi.map_det]
  exact (map_ne_zero_iff phi phi.injective).mpr hdet

end Transport

end LeanProofs.PolynomialFormulas.LazardQuintic
