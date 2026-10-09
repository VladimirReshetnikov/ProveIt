import GowersSzemeredi.Proofs16ColumnPairGluing
import GowersSzemeredi.Proofs16GlobalColumnAnchors

/-! Compatible representations for every pair in the dense column core,
constructed from the original bihomomorphism without new size costs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnPairDensity (alpha : Real) : Real :=
  (globalColumnWalkDensity alpha)^2*(globalColumnAnchorDensity alpha)^6/64

/-- The same dense core supports uniformly many representations for
single columns and pairs, with the ambient richness still available. -/
theorem global_column_pair_representations {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnRichnessModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let r := globalColumnRichnessRadius alpha
    let eta := globalColumnWalkDensity alpha
    let lambda := globalColumnAnchorDensity alpha
    let sigma := globalColumnPairDensity alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ B ⊆ X ∧ P ⊆ B ∧
      globalColumnVertexDensity alpha*N/2 ≤ (P.card : Real) ∧
      0 < eta ∧ 0 < r ∧ 0 < lambda ∧ 0 < sigma ∧
      (∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card) ∧
      (∀ a ∈ P, ∀ b ∈ P, sigma*(N : Real)^5 ≤ (columnPairRepresentations B T L r a b).card) ∧
      (∀ (U V : Finset (ZMod N)), U ⊆ B → V ⊆ B →
        ∀ (beta1 beta2 : Real), 0 ≤ beta1 → 0 ≤ beta2 →
          beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
          (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) := by
  obtain ⟨X,T,L,W,B,P,hsys,hW,hT,hL,hzero,hBX,hPB,hB,hP,heta,hr,hlambda,htriple,hrich⟩ :=
    global_popular_column_representations A phi ha ha1 hA hphi hN
  have hsigma : 0 < globalColumnPairDensity alpha := by
    unfold globalColumnPairDensity
    positivity
  refine ⟨X,T,L,W,B,P,hsys,hW,hT,hL,hzero,hBX,hPB,hP,heta,hr,hlambda,hsigma,htriple,?_,hrich⟩
  intro a ha b hb
  exact column_pair_representations_count B T L _ a b hlambda (htriple a ha) (htriple b hb) hrich

end LeanProofs.GowersSzemeredi
