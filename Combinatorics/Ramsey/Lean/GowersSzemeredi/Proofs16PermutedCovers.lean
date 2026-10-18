import GowersSzemeredi.Proofs16CoordinatePermutations

/-! This module keeps `Box.coordinateReindex_symm` and
`Box.coordinateReindex_symm'`; the rest of the development, with its
description, is in `Proofs16PermutedCoversSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

@[simp] theorem Box.coordinateReindex_symm {N k : Nat} (P : Box N k)
    (e : Fin k ≃ Fin k) : (P.coordinateReindex e).coordinateReindex e.symm = P := by
  cases P
  simp only [Box.coordinateReindex]
  congr 1
  funext i
  simp

@[simp] theorem Box.coordinateReindex_symm' {N k : Nat} (P : Box N k)
    (e : Fin k ≃ Fin k) : (P.coordinateReindex e.symm).coordinateReindex e = P := by
  simpa only [Equiv.symm_symm] using P.coordinateReindex_symm e.symm

end LeanProofs.GowersSzemeredi
