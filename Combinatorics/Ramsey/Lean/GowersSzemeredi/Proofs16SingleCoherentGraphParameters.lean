import GowersSzemeredi.Proofs16CoherentDensityControlledGraph
import GowersSzemeredi.Proofs16SingleFamilyRegularityInput

/-! Uniform graph thresholds for the constructed anchor family. Finite
suprema avoid any unproved monotonicity of an adaptive error schedule. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentUniformGraphModulusBound (power : Nat) (scale : Real) (H cells K : Nat)
    (rho : Real) (d : Nat) (kappa : Real) : Nat :=
  (Finset.range (K+1)).sup fun b => (Finset.range (K+1)).sup fun ell =>
    coherentAdaptiveGraphModulusBound (coherentDensityAccuracy H (coherentGraphFrequencyBound b ell) power scale)
      H (coherentGraphFrequencyBound b ell) cells ell rho (d,kappa)

theorem coherentUniformGraphModulusBound_spec (power : Nat) (scale : Real) (H cells K : Nat)
    (rho : Real) (d : Nat) (kappa : Real) {b ell N : Nat} (hb : b ≤ K) (hl : ell ≤ K)
    (hN : coherentUniformGraphModulusBound power scale H cells K rho d kappa ≤ N) :
    coherentAdaptiveGraphModulusBound (coherentDensityAccuracy H (coherentGraphFrequencyBound b ell) power scale)
      H (coherentGraphFrequencyBound b ell) cells ell rho (d,kappa) ≤ N := by
  exact (Finset.le_sup (f := fun l => coherentAdaptiveGraphModulusBound
    (coherentDensityAccuracy H (coherentGraphFrequencyBound b l) power scale)
    H (coherentGraphFrequencyBound b l) cells l rho (d,kappa))
    (Finset.mem_range.mpr (by omega : ell < K+1))).trans
    ((Finset.le_sup (f := fun c => (Finset.range (K+1)).sup fun l => coherentAdaptiveGraphModulusBound
      (coherentDensityAccuracy H (coherentGraphFrequencyBound c l) power scale)
      H (coherentGraphFrequencyBound c l) cells l rho (d,kappa))
      (Finset.mem_range.mpr (by omega : b < K+1))).trans hN)

def singleCoherentGraphCells : Nat := ⌈32*Real.pi⌉₊

theorem singleCoherentGraphCells_pos : 0 < singleCoherentGraphCells := Nat.ceil_pos.mpr (by positivity)

theorem singleCoherentGraphCells_spec : 4 ≤ (1/(8*Real.pi))*(singleCoherentGraphCells : Real) := by
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (by positivity)).mpr
  have h := Nat.le_ceil (32*Real.pi)
  change 4*(8*Real.pi) ≤ (⌈32*Real.pi⌉₊ : Real)
  nlinarith

def singleCoherentGraphH (d : Nat) (r : Real) : Nat :=
  ⌈(2 : Real)^(8*jointSelectionRank d r)/(jointSelectionRadius d r/2)⌉₊

theorem singleCoherentGraphH_pos (d : Nat) (r : Real) : 0 < singleCoherentGraphH d r := by
  have h := jointSelectionRadius_pos d r
  exact Nat.ceil_pos.mpr (by positivity)

theorem singleCoherentGraphH_spec (d : Nat) (r : Real) {ell : Nat} (hl : ell ≤ 8*jointSelectionRank d r) :
    (2 : Real)^ell ≤ (jointSelectionRadius d r/2)*(singleCoherentGraphH d r : Real) := by
  have hs := half_pos (jointSelectionRadius_pos d r)
  have hc : (2 : Real)^(8*jointSelectionRank d r)/(jointSelectionRadius d r/2) ≤ (singleCoherentGraphH d r : Real) := Nat.le_ceil _
  have h := (div_le_iff₀ hs).mp hc
  exact (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hl).trans (by simpa only [mul_comm] using h)

def singleCoherentGraphInitialRank (delta kappa : Real) (d : Nat) (r : Real) : Nat :=
  max (rowCommonBohrRank delta (uniformAnchorIndexDensity delta kappa d r) d r) (8*jointSelectionRank d r)

def singleCoherentGraphModulusBound (delta kappa : Real) (d : Nat) (r : Real)
    (power : Nat) (scale : Real) : Nat :=
  coherentUniformGraphModulusBound power scale (singleCoherentGraphH d r) singleCoherentGraphCells
    (8*jointSelectionRank d r) (1/(8*Real.pi)) (singleCoherentGraphInitialRank delta kappa d r)
    (singleProgressionDensity delta kappa d r)

end LeanProofs.GowersSzemeredi
