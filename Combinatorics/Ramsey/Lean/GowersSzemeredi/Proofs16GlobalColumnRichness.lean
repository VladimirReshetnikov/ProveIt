import GowersSzemeredi.Proofs16WalkAdditiveRichness
import GowersSzemeredi.Proofs16ColumnFourWalkSet

/-! A dense family of columns is additively rich in every pair of dense
subsets, directly from the original bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnWalkDensity (alpha : Real) : Real :=
  (globalColumnQuadrupleDensity alpha/4)^5/16384

def globalColumnRichnessModulusBound (alpha : Real) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  let rho := globalColumnIdentityRadius alpha
  max (globalColumnGraphModulusBound alpha)
    (refinementKernelCap (4*d) (6*d) rho (columnIdentityRadius d rho 1) + 1)

def globalColumnRichnessRadius (alpha : Real) : Real :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  let rho := globalColumnIdentityRadius alpha
  refinementKernelRadius (4*d) (6*d) rho (columnIdentityRadius d rho 1)

/-- Every pair of dense subsets of the constructed column set contains
quantitatively many exact mixed additive quadruples at one common radius. -/
theorem global_column_additive_richness {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnRichnessModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ B ⊆ X ∧
      3*(globalColumnQuadrupleDensity alpha/4)*N/8 ≤ (B.card : Real) ∧
      0 < globalColumnWalkDensity alpha ∧ 0 < globalColumnRichnessRadius alpha ∧
      (∀ (U V : Finset (ZMod N)), U ⊆ B → V ⊆ B →
        ∀ (beta1 beta2 : Real), 0 ≤ beta1 → 0 ≤ beta2 →
          beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
          (beta1*beta2*globalColumnWalkDensity alpha)^2*(N : Real)^3 ≤
            ((mixedExactColumnQuadruples U V T L (globalColumnRichnessRadius alpha)).card : Real)) := by
  have hNgraph : globalColumnGraphModulusBound alpha ≤ N := (le_max_left _ _).trans hN
  have hNker : refinementKernelCap (4*columnSpectrumCap (columnEightDensity alpha))
      (6*columnSpectrumCap (columnEightDensity alpha)) (globalColumnIdentityRadius alpha)
      (columnIdentityRadius (columnSpectrumCap (columnEightDensity alpha)) (globalColumnIdentityRadius alpha) 1) < N :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans hN)
  obtain ⟨X,T,L,W,E,B,hsys,hT,hL,hzero,hd,hr,hEX,hloop,hsym,hcoh,hBX,hB,hwalk⟩ :=
    global_column_four_walk_set A phi ha ha1 hA hphi hNgraph
  have hrho := globalColumnIdentityRadius_pos ha ha1
  have heta : 0 < globalColumnWalkDensity alpha := by
    unfold globalColumnWalkDensity
    positivity
  refine ⟨X,T,L,W,B,hsys,hT,hL,hzero,hBX,hB,heta,
    refinementKernelRadius_pos _ _ hrho hr, ?_⟩
  intro U V hUB hVB beta1 beta2 hb1 hb2 hU hV
  apply mixed_exact_quadruples_of_many_walks X U V T L E hrho hr
    (columnIdentityRadius_le _ _ 1) hb1 hb2 heta.le hU hV _ hT hL hzero hEX hcoh hNker
  intro u hu v hv
  simpa only [globalColumnWalkDensity, div_mul_eq_mul_div] using hwalk u (hUB hu) v (hVB hv)

end LeanProofs.GowersSzemeredi
