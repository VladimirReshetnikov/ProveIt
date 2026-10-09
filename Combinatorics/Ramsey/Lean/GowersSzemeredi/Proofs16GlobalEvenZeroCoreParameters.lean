import GowersSzemeredi.Proofs16EvenModelCoverZeroCore
import GowersSzemeredi.Proofs16GlobalZeroCoreParameters

/-! Density-only parameters for removing the global models of a fixed even length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def globalEvenColumnModelRank (alpha : Real) (k : Nat) : Nat :=
  ⌈((2*k : Nat)*columnSpectrumCap (columnEightDensity alpha) : Real)/globalColumnWordDensity alpha (2*k-1)⌉₊

def globalEvenColumnModelCount (alpha : Real) (k : Nat) : Nat :=
  ⌈1/globalColumnWordDensity alpha (2*k-1)⌉₊

def globalEvenColumnZeroRadius (alpha : Real) (k : Nat) : Real :=
  min (globalColumnModelRadius alpha (2*k-1))
    (refinementKernelRadius (globalEvenColumnModelRank alpha k)
      (columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnModelRadius alpha (2*k-1)/2))

def globalEvenColumnZeroDensity (alpha : Real) (k : Nat) : Real :=
  let beta := modelTestDensity (globalEvenColumnModelRank alpha k)
    (columnSpectrumCap (columnEightDensity alpha)) (globalColumnModelRadius alpha (2*k-1))
  (beta/(5*k))^(modelEliminationRounds beta (globalEvenColumnModelCount alpha k))*
    globalColumnVertexDensity alpha/2

def globalEvenColumnZeroModulusBound (alpha : Real) (k : Nat) : Nat :=
  max (globalColumnModelModulusBound alpha (2*k-1))
    (max (refinementKernelCap (globalEvenColumnModelRank alpha k)
      (columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnModelRadius alpha (2*k-1)/2)+1) 7)

theorem globalEvenColumnZeroRadius_pos {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalEvenColumnZeroRadius alpha k := by
  exact lt_min (globalColumnModelRadius_pos ha ha1 (2*k-1))
    (refinementKernelRadius_pos _ _ (globalColumnIdentityRadius_pos ha ha1)
      (div_pos (globalColumnModelRadius_pos ha ha1 (2*k-1)) (by norm_num)))

theorem globalEvenColumnZeroRadius_le {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalEvenColumnZeroRadius alpha k ≤ globalColumnIdentityRadius alpha :=
  (min_le_left _ _).trans (globalColumnModelRadius_le ha ha1 (2*k-1))

theorem globalEvenColumnZeroDensity_pos {alpha : Real} {k : Nat} [NeZero k] (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalEvenColumnZeroDensity alpha k := by
  have hk : (0 : Real) < k := by exact_mod_cast NeZero.pos k
  have hb := modelTestDensity_pos (globalEvenColumnModelRank alpha k)
    (columnSpectrumCap (columnEightDensity alpha)) (globalColumnModelRadius_pos ha ha1 (2*k-1))
  have hv := globalColumnVertexDensity_pos ha ha1
  unfold globalEvenColumnZeroDensity
  positivity

end LeanProofs.GowersSzemeredi
