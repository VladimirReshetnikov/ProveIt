import GowersSzemeredi.Proofs16ColumnWordIdentityParameters

/-! Dense compatible representations with identities on only anchor and
output domains, at an explicit length-dependent radius and modulus bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- For any fixed word length, the original bihomomorphism gives a dense
core with many representations and no intermediate-domain conditions. -/
theorem global_column_word_identities {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (k : Nat) (hN : globalColumnWordIdentityModulusBound alpha k ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let r := globalColumnRichnessRadius alpha
    let eta := globalColumnWalkDensity alpha
    let lambda := globalColumnAnchorDensity alpha
    let sigma := globalColumnWordDensity alpha
    let s := globalColumnWordIdentityRadius alpha k
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
      0 < eta ∧ 0 < r ∧ 0 < lambda ∧ (∀ j, 0 < sigma j) ∧ 0 < s ∧
      (∀ a ∈ P, lambda*(N : Real)^2 ≤ (columnTripleRepresentations B T L r a).card) ∧
      (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) →
        sigma as.length*(N : Real)^(3*as.length+2) ≤
          (columnWordRepresentations B T L r (a::as)).card) ∧
      (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) → as.length = k →
        ∀ w ∈ columnWordRepresentations B T L r (a::as), ColumnWordIdentity T L s (a::as) w) ∧
      (∀ (U V : Finset (ZMod N)), U ⊆ B → V ⊆ B →
        ∀ (beta1 beta2 : Real), 0 ≤ beta1 → 0 ≤ beta2 →
          beta1*N ≤ (U.card : Real) → beta2*N ≤ (V.card : Real) →
          (beta1*beta2*eta)^2*(N : Real)^3 ≤ ((mixedExactColumnQuadruples U V T L r).card : Real)) := by
  have hNrich : globalColumnRichnessModulusBound alpha ≤ N := (le_max_left _ _).trans hN
  have hNker : refinementKernelCap (4*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      (2*k*columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnRichnessRadius alpha) < N :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans hN)
  obtain ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,heta,hr,hlambda,hsigma,htriple,hwords,hrich⟩ :=
    global_column_word_representations A phi ha ha1 hA hphi hNrich
  refine ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,heta,hr,hlambda,hsigma,
    globalColumnWordIdentityRadius_pos ha ha1 k,htriple,hwords,?_,hrich⟩
  intro a as has hlen w hw
  have hcap : refinementKernelCap (4*(as.length+1)*columnSpectrumCap (columnEightDensity alpha))
      (2*as.length*columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnRichnessRadius alpha) < N := by
    simpa only [hlen] using hNker
  have h := column_word_identity_remove_aux X B T L (globalColumnIdentityRadius_pos ha ha1)
    hr (globalColumnRichnessRadius_le ha ha1) hBX hT hL hzero a as
    (fun x hx => hBX (hPB (has x hx))) w hw hcap
  simpa only [hlen,globalColumnWordIdentityRadius] using h

end LeanProofs.GowersSzemeredi
