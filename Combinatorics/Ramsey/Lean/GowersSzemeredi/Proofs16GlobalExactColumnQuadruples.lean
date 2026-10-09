import GowersSzemeredi.Proofs16GlobalColumnWitnessSystem
import GowersSzemeredi.Proofs16ManyExactColumnQuadruples

/-! A dense Freiman bihomomorphism produces many exact additive column
identities, with all parameters depending only on the initial density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnQuadrupleDensity (alpha : Real) : Real :=
  (columnWitnessDensity (columnEightDensity alpha))^4 * (alpha / (2 - alpha))^4 / 2

def globalColumnIdentityModulusBound (alpha : Real) : Nat :=
  sharedWitnessImageCap (columnSpectrumCap (columnEightDensity alpha))
    (1 / (4 * Real.pi)) (globalColumnQuadrupleDensity alpha) + 1

def globalColumnIdentityRadius (alpha : Real) : Real :=
  sharedWitnessKernelRadius (columnSpectrumCap (columnEightDensity alpha))
    (1 / (4 * Real.pi)) (globalColumnQuadrupleDensity alpha)

theorem globalColumnQuadrupleDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnQuadrupleDensity alpha := by
  have hc := columnWitnessDensity_pos (columnEightDensity_pos ha)
  have hb : 0 < alpha / (2 - alpha) := div_pos ha (by linarith)
  unfold globalColumnQuadrupleDensity
  positivity

theorem globalColumnIdentityRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnIdentityRadius alpha :=
  sharedWitnessKernelRadius_pos _ (by positivity) (globalColumnQuadrupleDensity_pos ha ha1)

/-- Starting with global density and a Freiman bihomomorphism, construct
a dense family of represented column maps with many exact index
quadruples. No witness-system or bounded-image hypothesis remains. -/
theorem global_many_exact_column_quadruples {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnIdentityModulusBound alpha ≤ N) :
    let beta := columnEightDensity alpha
    let d := columnSpectrumCap beta
    let c := columnWitnessDensity beta
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1 / (4 * Real.pi))) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ (∀ x ∈ X, c * (N : Real)^4 ≤ (W x).card) ∧
      0 < globalColumnIdentityRadius alpha ∧ 0 < globalColumnQuadrupleDensity alpha ∧
      globalColumnQuadrupleDensity alpha * (N : Real)^3 ≤
        ((exactColumnQuadruples X T L (globalColumnIdentityRadius alpha)).card : Real) := by
  obtain ⟨X, T, L, W, hX, hsys, hT, hL, hzero, hW⟩ :=
    dense_bihom_column_witness_system A phi ha ha1 hA hphi
  have hb : 0 < alpha / (2 - alpha) := div_pos ha (by linarith)
  have hc := columnWitnessDensity_pos (columnEightDensity_pos ha)
  have hN' : sharedWitnessImageCap (columnSpectrumCap (columnEightDensity alpha))
      (1 / (4 * Real.pi)) (globalColumnQuadrupleDensity alpha) < N := by
    exact Nat.lt_of_succ_le hN
  have hmany := many_exact_column_quadruples A phi X T L W (by positivity) hc hb
    hphi hsys hT hL hzero hW hX hN'
  exact ⟨X, T, L, W, hX, hsys, hT, hL, hzero, hW,
    hmany.1, globalColumnQuadrupleDensity_pos ha ha1, hmany.2⟩

end LeanProofs.GowersSzemeredi
