import GowersSzemeredi.Proofs16ColumnTripleRepresentations

/-! A dense set of popular columns with many exact three-term
representations, retaining hereditary richness for later composition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnVertexDensity (alpha : Real) : Real :=
  3*(globalColumnQuadrupleDensity alpha/4)/8

def globalColumnAnchorDensity (alpha : Real) : Real :=
  (globalColumnWalkDensity alpha)^2*(globalColumnVertexDensity alpha)^3/16

theorem globalColumnVertexDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnVertexDensity alpha := by
  have h := globalColumnQuadrupleDensity_pos ha ha1
  unfold globalColumnVertexDensity
  positivity

/-- The popular columns form a dense core. Each has many index and map
representations by triples in the ambient rich column set. -/
theorem global_popular_column_representations {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnRichnessModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let r := globalColumnRichnessRadius alpha
    let eta := globalColumnWalkDensity alpha
    let b := globalColumnVertexDensity alpha
    let lambda := globalColumnAnchorDensity alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ B ⊆ X ∧ P ⊆ B ∧
      b*N ≤ (B.card : Real) ∧ b*N/2 ≤ (P.card : Real) ∧
      0 < eta ∧ 0 < r ∧ 0 < lambda ∧
      (∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card) ∧
      (∀ (U V : Finset (ZMod N)), U ⊆ B → V ⊆ B →
        ∀ (beta1 beta2 : Real), 0 ≤ beta1 → 0 ≤ beta2 →
          beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
          (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) := by
  obtain ⟨X,T,L,W,B,hsys,hT,hL,hzero,hBX,hB,heta,hr,hrich⟩ :=
    global_column_additive_richness A phi ha ha1 hA hphi hN
  have hb := globalColumnVertexDensity_pos ha ha1
  have hB' : globalColumnVertexDensity alpha*N ≤ (B.card : Real) := by
    dsimp only [globalColumnVertexDensity]
    nlinarith [hB]
  have hcard := exact_quadruples_richness_card B T L (globalColumnRichnessRadius alpha)
    (globalColumnWalkDensity alpha) (fun C hCB beta hbeta hc => hrich C C hCB hCB beta beta hbeta hbeta hc hc)
  let P := popularColumnAnchors B T L (globalColumnRichnessRadius alpha) (globalColumnAnchorDensity alpha)
  have hP : globalColumnVertexDensity alpha*N/2 ≤ (P.card : Real) :=
    popular_column_anchors_dense B T L _ hb heta hB' hcard
  have hlambda : 0 < globalColumnAnchorDensity alpha := by
    unfold globalColumnAnchorDensity
    positivity
  exact ⟨X,T,L,W,B,P,hsys,hT,hL,hzero,hBX,Finset.filter_subset _ _,hB',hP,
    heta,hr,hlambda,fun a ha => popular_column_triple_count B T L _ _ ha,hrich⟩

end LeanProofs.GowersSzemeredi
