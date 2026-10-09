import GowersSzemeredi.Proofs16ColumnWordIdentity
import GowersSzemeredi.Proofs16GlobalColumnWordRepresentations

/-! Explicit parameters for identities of words of a fixed length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem refinementKernelRadius_le_rho (d e : Nat) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) : refinementKernelRadius d e rho r ≤ rho := by
  have hK : (1 : Real) ≤ refinementKernelCap d e rho r := by
    exact_mod_cast refinementKernelCap_pos d e hrho hr
  unfold refinementKernelRadius
  apply (div_le_iff₀ (by linarith : (0 : Real) < refinementKernelCap d e rho r)).mpr
  nlinarith

def globalColumnWordIdentityRadius (alpha : Real) (k : Nat) : Real :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  refinementKernelRadius (4*(k+1)*d) (2*k*d)
    (globalColumnIdentityRadius alpha) (globalColumnRichnessRadius alpha)

def globalColumnWordIdentityModulusBound (alpha : Real) (k : Nat) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  max (globalColumnRichnessModulusBound alpha)
    (refinementKernelCap (4*(k+1)*d) (2*k*d)
      (globalColumnIdentityRadius alpha) (globalColumnRichnessRadius alpha) + 1)

theorem globalColumnRichnessRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnRichnessRadius alpha :=
  refinementKernelRadius_pos _ _ (globalColumnIdentityRadius_pos ha ha1)
    (columnIdentityRadius_pos _ (globalColumnIdentityRadius_pos ha ha1) 1)

theorem globalColumnRichnessRadius_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnRichnessRadius alpha ≤ globalColumnIdentityRadius alpha :=
  refinementKernelRadius_le_rho _ _ (globalColumnIdentityRadius_pos ha ha1)
    (columnIdentityRadius_pos _ (globalColumnIdentityRadius_pos ha ha1) 1)

theorem globalColumnWordIdentityRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (k : Nat) :
    0 < globalColumnWordIdentityRadius alpha k :=
  refinementKernelRadius_pos _ _ (globalColumnIdentityRadius_pos ha ha1) (globalColumnRichnessRadius_pos ha ha1)

end LeanProofs.GowersSzemeredi
