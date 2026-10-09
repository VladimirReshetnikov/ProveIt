import GowersSzemeredi.Proofs16GlobalZeroCoreParameters

/-! All additive column quadruples vanish on an explicit dense core,
starting from the original dense bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The complete global construction followed by finite model elimination.
Every parameter is a function of the original density alone. -/
theorem global_zero_column_core {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnZeroModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let s := globalColumnZeroRadius alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (P Gamma : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ P ⊆ X ∧ P.Nonempty ∧
      globalColumnZeroDensity alpha*N ≤ (P.card : Real) ∧
      Gamma.card ≤ globalColumnModelRank alpha ∧
      ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ P) → q 0-q 1+q 2-q 3 = 0 →
        ∀ y ∈ bohr Gamma s, (∀ i, y ∈ bohr (T (q i)) s) → columnQuadValue L q y = 0 := by
  let d := columnSpectrumCap (columnEightDensity alpha)
  let g := globalColumnModelRank alpha
  let r := globalColumnModelRadius alpha 3
  let beta := modelTestDensity g d r
  let t := modelEliminationRounds beta (globalColumnModelCount alpha)
  have hNm : globalColumnModelModulusBound alpha 3 ≤ N := (le_max_left _ _).trans hN
  have hNk : refinementKernelCap g d (globalColumnIdentityRadius alpha) (r/2) < N :=
    Nat.lt_of_succ_le ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have h7 : 7 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨X,T,L,W,B,P,hsys,hW,hT,hL,hzero,hBX,hPB,hP,hdelta,hr,_,hmodels⟩ :=
    global_column_models A phi ha ha1 hA hphi 3 hNm
  obtain ⟨J,_,hJ,Gamma,_,hG,hf,hcover⟩ := hmodels 0
  have hGamma : Gamma.card ≤ g := by
    apply (Nat.cast_le (α := Real)).mp
    calc (Gamma.card : Real) ≤ (4*d : Real)/globalColumnWordDensity alpha 3 :=
        (le_div_iff₀ hdelta).mpr (by norm_num only [Nat.cast_ofNat,show (3 : Real)+1 = 4 by norm_num] at hG; exact hG)
      _ ≤ (g : Real) := Nat.le_ceil _
  have hJcard : J.card ≤ globalColumnModelCount alpha := by
    apply (Nat.cast_le (α := Real)).mp
    exact ((le_div_iff₀ hdelta).mpr hJ).trans (Nat.le_ceil _)
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hv := globalColumnVertexDensity_pos ha ha1
    have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hp : (0 : Real) < P.card := (by positivity : 0 < globalColumnVertexDensity alpha*N/2).trans_le hP
    exact_mod_cast hp
  obtain ⟨Q,hQP,hQne,hQ,hquad⟩ := column_model_cover_zero_core P J Gamma T L
    (fun j y => columnAnchorEval (fun x => L x y) (columnAnchorList j))
    (globalColumnIdentityRadius_pos ha ha1) hr (globalColumnModelRadius_le ha ha1 3)
    hPne hGamma hJcard (fun x hx => hT x (hBX (hPB hx)))
    (fun j hj => (hf j hj).1) (fun j hj => (hf j hj).2) hNk h7
    (fun a ha => by obtain ⟨j,hj,_,hc⟩ := hcover a ha; exact ⟨j,hj,hc⟩)
  refine ⟨X,T,L,W,Q,Gamma,hsys,hW,hT,hL,hzero,
    fun x hx => hBX (hPB (hQP hx)),hQne,?_,hGamma,hquad⟩
  have hb : 0 < beta := modelTestDensity_pos g d hr
  calc
    globalColumnZeroDensity alpha*N = (beta/10)^t*(globalColumnVertexDensity alpha*N/2) := by
      dsimp [globalColumnZeroDensity,beta,t,g,d,r]
      ring
    _ ≤ (beta/10)^t*P.card := mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ Q.card := hQ

end LeanProofs.GowersSzemeredi
