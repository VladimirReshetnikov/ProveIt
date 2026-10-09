import GowersSzemeredi.Proofs16FourfoldBohrExtension

/-! Uniform parameters for localizing a dense graph overlap before
retaining its mixed configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def commonDifferenceRadius (kappa : Real) : Real := kappa/(32*Real.pi)
def commonDifferenceRank (kappa : Real) : Nat := ⌈16*kappa^(-(2 : Real))⌉₊
def commonDifferenceCells (kappa : Real) : Nat := ⌈8/commonDifferenceRadius kappa⌉₊
def commonDifferenceClusterDensity (kappa : Real) : Real :=
  kappa/(commonDifferenceCells kappa : Real)^commonDifferenceRank kappa
def commonDifferenceBohrDensity (kappa : Real) : Real :=
  (commonDifferenceClusterDensity kappa)^2*kappa

theorem commonDifferenceRadius_pos {kappa : Real} (hk : 0 < kappa) :
    0 < commonDifferenceRadius kappa := by unfold commonDifferenceRadius; positivity

theorem commonDifferenceCells_pos {kappa : Real} (hk : 0 < kappa) :
    0 < commonDifferenceCells kappa := Nat.ceil_pos.mpr (div_pos (by norm_num) (commonDifferenceRadius_pos hk))

theorem commonDifferenceClusterDensity_pos {kappa : Real} (hk : 0 < kappa) :
    0 < commonDifferenceClusterDensity kappa := by
  have hM : (0 : Real) < commonDifferenceCells kappa := by exact_mod_cast commonDifferenceCells_pos hk
  exact div_pos hk (pow_pos hM _)

theorem commonDifferenceBohrDensity_pos {kappa : Real} (hk : 0 < kappa) :
    0 < commonDifferenceBohrDensity kappa :=
  mul_pos (pow_pos (commonDifferenceClusterDensity_pos hk) 2) hk

/-- The rank ceiling makes the cluster density independent of the
particular spectrum returned by the extension theorem. -/
theorem commonDifferenceClusterDensity_le {N : Nat} (Gamma : Finset (ZMod N))
    {kappa : Real} (hk : 0 < kappa) (hG : (Gamma.card : Real) ≤ 16*kappa^(-(2 : Real))) :
    commonDifferenceClusterDensity kappa ≤ kappa/(commonDifferenceCells kappa : Real)^Gamma.card := by
  have hG' : Gamma.card ≤ commonDifferenceRank kappa := by
    exact (Nat.cast_le (α := Real)).mp (hG.trans (Nat.le_ceil _))
  have hM : (1 : Real) ≤ commonDifferenceCells kappa := by
    exact_mod_cast commonDifferenceCells_pos hk
  exact div_le_div_of_nonneg_left hk.le (by positivity) (pow_le_pow_right₀ hM hG')

end LeanProofs.GowersSzemeredi
