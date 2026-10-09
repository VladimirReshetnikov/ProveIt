import GowersSzemeredi.Proofs16CoherentBridgeConstruction
import GowersSzemeredi.Proofs16SingleCoherentGraphParameters

/-! Uniform modulus bounds for the actual anchor family's radius chain.
Every finite choice of fixed and varying frequency cardinalities is covered. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentBridgeModulusBound (b ell cells d depth power : Nat) (rho sigma kappa scale : Real) : Nat :=
  let H := coherentRadiusProfileCells sigma ell depth
  let m := coherentGraphFrequencyBound b ell
  let k := 4*(b+4*ell*ell+ell)
  let e := fun a : Nat × Real => coherentBridgeAccuracy H m k (a.2^power/scale)
  coherentAdaptiveGraphModulusBound e H m cells ell rho (d,kappa)

def singleCoherentBridgeModulusBound (delta kappa : Real) (d : Nat) (r : Real)
    (depth power : Nat) (scale : Real) : Nat :=
  let K := 8*jointSelectionRank d r
  (Finset.range (K+1)).sup fun b => (Finset.range (K+1)).sup fun ell =>
    coherentBridgeModulusBound b ell singleCoherentGraphCells (singleCoherentGraphInitialRank delta kappa d r)
      depth power (1/(8*Real.pi)) (jointSelectionRadius d r/2) (singleProgressionDensity delta kappa d r) scale

theorem singleCoherentBridgeModulusBound_spec (delta kappa : Real) (d : Nat) (r : Real)
    (depth power : Nat) (scale : Real) {b ell N : Nat}
    (hb : b ≤ 8*jointSelectionRank d r) (hl : ell ≤ 8*jointSelectionRank d r)
    (hN : singleCoherentBridgeModulusBound delta kappa d r depth power scale ≤ N) :
    coherentBridgeModulusBound b ell singleCoherentGraphCells (singleCoherentGraphInitialRank delta kappa d r)
      depth power (1/(8*Real.pi)) (jointSelectionRadius d r/2) (singleProgressionDensity delta kappa d r) scale ≤ N := by
  let f := fun b ell => coherentBridgeModulusBound b ell singleCoherentGraphCells
    (singleCoherentGraphInitialRank delta kappa d r) depth power (1/(8*Real.pi))
    (jointSelectionRadius d r/2) (singleProgressionDensity delta kappa d r) scale
  exact (Finset.le_sup (f := f b) (Finset.mem_range.mpr (by omega : ell < 8*jointSelectionRank d r+1))).trans
    ((Finset.le_sup (f := fun b => (Finset.range (8*jointSelectionRank d r+1)).sup (f b))
      (Finset.mem_range.mpr (by omega : b < 8*jointSelectionRank d r+1))).trans hN)

end LeanProofs.GowersSzemeredi
