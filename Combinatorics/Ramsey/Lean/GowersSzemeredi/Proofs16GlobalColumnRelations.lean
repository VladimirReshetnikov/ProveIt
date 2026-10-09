import GowersSzemeredi.Proofs16GlobalExactColumnQuadruples
import GowersSzemeredi.Proofs16ColumnRelationCounting

/-! Dense column relations and their finite composition hierarchy follow
from the original dense bihomomorphism, with a density-only threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnCompositionModulusBound (alpha : Real) (n : Nat) : Nat :=
  max (globalColumnIdentityModulusBound alpha)
    (columnIdentityModulusBound (columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) n)

theorem globalColumnIdentityRadius_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    globalColumnIdentityRadius alpha ≤ 1 / (4 * Real.pi) := by
  have hK : (1 : Real) ≤ sharedWitnessImageCap (columnSpectrumCap (columnEightDensity alpha))
      (1 / (4 * Real.pi)) (globalColumnQuadrupleDensity alpha) := by
    exact_mod_cast sharedWitnessImageCap_pos _ (by positivity)
      (globalColumnQuadrupleDensity_pos ha ha1)
  change ((1 / (4 * Real.pi)) / 2) / _ ≤ _
  have h : (0 : Real) < 1 / (4 * Real.pi) := by positivity
  exact (div_le_self (by positivity) hK).trans (by linarith)

/-- Construct dense level-one relations and all compositions through a
prescribed finite number of levels, retaining their original witnesses.
The size threshold depends only on density and the number of levels. -/
theorem global_dense_column_relations {N n : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnCompositionModulusBound alpha n ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha) * (N : Real)^4 ≤ (W x).card) ∧
      0 < rho ∧ 0 < globalColumnQuadrupleDensity alpha ∧
      globalColumnQuadrupleDensity alpha * (N : Real)^3 ≤
        ((columnRelationPairs X T L rho).card : Real) ∧
      (∀ (i j : Nat) (p q z : ZMod N × ZMod N), 0 < i → 0 < j → i+j ≤ n →
        ColumnRelationLevel X T L d rho i p q → ColumnRelationLevel X T L d rho j q z →
        ColumnRelationLevel X T L d rho (i+j) p z) := by
  have hN0 := (le_max_left _ _).trans hN
  have hNlevels := (le_max_right _ _).trans hN
  obtain ⟨X, T, L, W, hX, hsys, hT, hL, hzero, hW, hrho, htheta, hmany⟩ :=
    global_many_exact_column_quadruples A phi ha ha1 hA hphi hN0
  have hL' : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (globalColumnIdentityRadius alpha)) (L x) :=
    fun x hx => (hL x hx).mono (bohr_mono_radius _ (globalColumnIdentityRadius_le ha ha1))
  refine ⟨X, T, L, W, hX, hsys, hL, hT, hL', hzero, hW, hrho, htheta, ?_, ?_⟩
  · rw [columnRelationPairs_card_eq]
    exact hmany
  · intro i j p q z hi hj hij hpq hqz
    exact columnRelationLevel_trans X T L hrho hT hL' hzero hpq hqz hi hj hij hNlevels

end LeanProofs.GowersSzemeredi
