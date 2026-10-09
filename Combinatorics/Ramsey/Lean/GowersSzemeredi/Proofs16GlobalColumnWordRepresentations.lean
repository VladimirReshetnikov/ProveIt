import GowersSzemeredi.Proofs16ColumnWordDensity
import GowersSzemeredi.Proofs16GlobalColumnAnchors

/-! Compatible representations for arbitrary nonempty lists in the dense
column core, constructed from the original bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnWordDensity (alpha : Real) (k : Nat) : Real :=
  columnWordDensity (globalColumnAnchorDensity alpha) (globalColumnWalkDensity alpha) k

/-- Every nonempty anchor list in the same dense core has uniformly many
compatible representations, with the ambient richness still available. -/
theorem global_column_word_representations {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnRichnessModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let r := globalColumnRichnessRadius alpha
    let eta := globalColumnWalkDensity alpha
    let lambda := globalColumnAnchorDensity alpha
    let sigma := globalColumnWordDensity alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ B ⊆ X ∧ P ⊆ B ∧
      globalColumnVertexDensity alpha*N/2 ≤ (P.card : Real) ∧
      0 < eta ∧ 0 < r ∧ 0 < lambda ∧ (∀ k, 0 < sigma k) ∧
      (∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card) ∧
      (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) →
        sigma as.length*(N : Real)^(3*as.length+2) ≤
          (columnWordRepresentations B T L r (a::as)).card) ∧
      (∀ (U V : Finset (ZMod N)), U ⊆ B → V ⊆ B →
        ∀ (beta1 beta2 : Real), 0 ≤ beta1 → 0 ≤ beta2 →
          beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
          (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) := by
  obtain ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hB,hP,heta,hr,hlambda,htriple,hrich⟩ :=
    global_popular_column_representations A phi ha ha1 hA hphi hN
  have hsigma : ∀ k, 0 < globalColumnWordDensity alpha k :=
    columnWordDensity_pos hlambda heta
  refine ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,heta,hr,hlambda,hsigma,htriple,?_,hrich⟩
  intro a as has
  exact column_word_representations_count B P T L _ hlambda heta htriple hrich a as has

end LeanProofs.GowersSzemeredi
