import GowersSzemeredi.Proofs16CoherentAnchorSystem

/-! Explicit parameters of coherent anchors obtained from the even core.
These preserve the existing elimination losses; no polynomial bound on
these composite functions is asserted. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def globalCoherentAnchorTolerance (alpha : Real) : Real :=
  (globalEvenColumnZeroDensity alpha 4)^16/10
def globalCoherentAnchorDensity (alpha : Real) : Real :=
  (globalEvenColumnZeroDensity alpha 4)^16/4
def globalCoherentAnchorRank (alpha : Real) : Nat :=
  globalEvenColumnModelRank alpha 4+columnSpectrumCap (columnEightDensity alpha)
def globalCoherentAnchorModulusBound (alpha : Real) : Nat :=
  max (globalEvenColumnZeroModulusBound alpha 4)
    ⌈16/(globalEvenColumnZeroDensity alpha 4)^16⌉₊

theorem globalCoherentAnchorTolerance_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalCoherentAnchorTolerance alpha := by
  have h := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  unfold globalCoherentAnchorTolerance
  positivity

theorem globalCoherentAnchorDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalCoherentAnchorDensity alpha := by
  have h := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  unfold globalCoherentAnchorDensity
  positivity

theorem globalCoherentAnchorModulusBound_mass {alpha : Real} {N : Nat}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hN : globalCoherentAnchorModulusBound alpha ≤ N) :
    16 ≤ (globalEvenColumnZeroDensity alpha 4)^16*(N : Real) := by
  have hb := globalEvenColumnZeroDensity_pos (k := 4) ha ha1
  have hn : 16/(globalEvenColumnZeroDensity alpha 4)^16 ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  simpa only [mul_comm] using (div_le_iff₀ (pow_pos hb 16)).mp hn

theorem globalEvenColumnZeroRadius_lt_four {alpha : Real} {k : Nat}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) : globalEvenColumnZeroRadius alpha k < 4 := by
  apply ((globalEvenColumnZeroRadius_le ha ha1).trans (globalColumnIdentityRadius_le ha ha1)).trans_lt
  apply (div_lt_iff₀ (show 0 < 4*Real.pi by positivity)).mpr
  nlinarith [Real.pi_gt_three]

end LeanProofs.GowersSzemeredi
