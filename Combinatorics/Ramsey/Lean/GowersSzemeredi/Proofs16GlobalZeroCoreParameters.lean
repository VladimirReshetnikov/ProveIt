import GowersSzemeredi.Proofs16ModelCoverZeroCore

/-! Density-only parameters for removing the global four-term models. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def globalColumnModelRank (alpha : Real) : Nat :=
  ⌈(4*columnSpectrumCap (columnEightDensity alpha) : Real)/globalColumnWordDensity alpha 3⌉₊

def globalColumnModelCount (alpha : Real) : Nat :=
  ⌈1/globalColumnWordDensity alpha 3⌉₊

def globalColumnZeroRadius (alpha : Real) : Real :=
  min (globalColumnModelRadius alpha 3)
    (refinementKernelRadius (globalColumnModelRank alpha)
      (columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnModelRadius alpha 3/2))

def globalColumnZeroDensity (alpha : Real) : Real :=
  let beta := modelTestDensity (globalColumnModelRank alpha)
    (columnSpectrumCap (columnEightDensity alpha)) (globalColumnModelRadius alpha 3)
  (beta/10)^(modelEliminationRounds beta (globalColumnModelCount alpha))*
    globalColumnVertexDensity alpha/2

def globalColumnZeroModulusBound (alpha : Real) : Nat :=
  max (globalColumnModelModulusBound alpha 3)
    (max (refinementKernelCap (globalColumnModelRank alpha)
      (columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnModelRadius alpha 3/2)+1) 7)

theorem globalColumnModelRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    0 < globalColumnModelRadius alpha k :=
  refinementKernelRadius_pos _ _ (globalColumnIdentityRadius_pos ha ha1)
    (globalColumnWordIdentityRadius_pos ha ha1 k)

theorem globalColumnModelRadius_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    globalColumnModelRadius alpha k ≤ globalColumnIdentityRadius alpha :=
  refinementKernelRadius_le_rho _ _ (globalColumnIdentityRadius_pos ha ha1)
    (globalColumnWordIdentityRadius_pos ha ha1 k)

theorem globalColumnZeroRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnZeroRadius alpha := by
  exact lt_min (globalColumnModelRadius_pos ha ha1 3)
    (refinementKernelRadius_pos _ _ (globalColumnIdentityRadius_pos ha ha1)
      (div_pos (globalColumnModelRadius_pos ha ha1 3) (by norm_num)))

theorem globalColumnZeroRadius_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnZeroRadius alpha ≤ globalColumnIdentityRadius alpha :=
  (min_le_left _ _).trans (globalColumnModelRadius_le ha ha1 3)

theorem globalColumnZeroDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnZeroDensity alpha := by
  have hb := modelTestDensity_pos (globalColumnModelRank alpha)
    (columnSpectrumCap (columnEightDensity alpha)) (globalColumnModelRadius_pos ha ha1 3)
  have hv := globalColumnVertexDensity_pos ha ha1
  unfold globalColumnZeroDensity
  positivity

end LeanProofs.GowersSzemeredi
