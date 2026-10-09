import GowersSzemeredi.Proofs16GlobalEvenZeroCoreParameters
import GowersSzemeredi.Proofs16EvenColumnRelations

/-! All additive alternating column lists of a fixed even length vanish on an explicit dense core,
starting from the original dense bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The complete global construction followed by finite model elimination.
Every parameter is a function of the original density and maximum arity.
All shorter even identities hold on the same core and the same domains. -/
theorem global_even_zero_column_core {N k : Nat} [NeZero N] [Fact N.Prime] [NeZero k]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalEvenColumnZeroModulusBound alpha k ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let s := globalEvenColumnZeroRadius alpha k
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (P Gamma : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ P ⊆ X ∧ P.Nonempty ∧
      globalEvenColumnZeroDensity alpha k*N ≤ (P.card : Real) ∧
      Gamma.card ≤ globalEvenColumnModelRank alpha k ∧
      ∀ m ≤ k, ∀ as : List (ZMod N), as.length = 2*m → (∀ x ∈ as, x ∈ P) → columnAnchorEval id as = 0 →
        ∀ y ∈ bohr Gamma s, (∀ x ∈ as, y ∈ bohr (T x) s) →
          columnAnchorEval (fun x => L x y) as = 0 := by
  let d := columnSpectrumCap (columnEightDensity alpha)
  let g := globalEvenColumnModelRank alpha k
  let r := globalColumnModelRadius alpha (2*k-1)
  let beta := modelTestDensity g d r
  let t := modelEliminationRounds beta (globalEvenColumnModelCount alpha k)
  have hNm : globalColumnModelModulusBound alpha (2*k-1) ≤ N := (le_max_left _ _).trans hN
  have hNk : refinementKernelCap g d (globalColumnIdentityRadius alpha) (r/2) < N :=
    Nat.lt_of_succ_le ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have h7 : 7 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,hdelta,hr,_,hmodels⟩ :=
    global_column_models A phi ha ha1 hA hphi (2*k-1) hNm
  obtain ⟨J,_,hJ,Gamma,_,hG,hf,hcover⟩ := hmodels 0
  have hlen : (2*k-1)+1 = 2*k := by have hk := NeZero.pos k; omega
  have hlenR : ((2*k-1 : Nat) : Real)+1 = (2*k : Nat) := by exact_mod_cast hlen
  have hk : (0 : Real) < k := by exact_mod_cast NeZero.pos k
  have hGamma : Gamma.card ≤ g := by
    apply (Nat.cast_le (α := Real)).mp
    calc (Gamma.card : Real) ≤ ((2*k : Nat)*d : Real)/globalColumnWordDensity alpha (2*k-1) :=
        (le_div_iff₀ hdelta).mpr (by simpa only [hlenR] using hG)
      _ ≤ (g : Real) := Nat.le_ceil _
  have hJcard : J.card ≤ globalEvenColumnModelCount alpha k := by
    apply (Nat.cast_le (α := Real)).mp
    exact ((le_div_iff₀ hdelta).mpr hJ).trans (Nat.le_ceil _)
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hv := globalColumnVertexDensity_pos ha ha1
    have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hp : (0 : Real) < P.card := (by positivity : 0 < globalColumnVertexDensity alpha*N/2).trans_le hP
    exact_mod_cast hp
  obtain ⟨Q,hQP,hQne,hQ,hquad⟩ := even_model_cover_zero_core (k := k) P J Gamma T L
    (fun j y => columnAnchorEval (fun x => L x y) (columnAnchorList j))
    (globalColumnIdentityRadius_pos ha ha1) hr (globalColumnModelRadius_le ha ha1 (2*k-1))
    hPne hGamma hJcard (fun x hx => hT x (hBX (hPB hx)))
    (fun j hj => (hf j hj).1) (fun j hj => (hf j hj).2) hNk h7
    (fun a ha => by obtain ⟨j,hj,_,hc⟩ := hcover a ha; exact ⟨j,hj,hc⟩)
  refine ⟨X,T,L,W,Q,Gamma,hsys,hLfull,hW,hT,hL,hzero,
    fun x hx => hBX (hPB (hQP hx)),hQne,?_,hGamma,fun m hm => even_zero_relations_mono Q Gamma T L _ hm hquad⟩
  have hb : 0 < beta := modelTestDensity_pos g d hr
  calc
    globalEvenColumnZeroDensity alpha k*N = (beta/(5*k))^t*(globalColumnVertexDensity alpha*N/2) := by
      dsimp [globalEvenColumnZeroDensity,beta,t,g,d,r]
      ring
    _ ≤ (beta/(5*k))^t*P.card := mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ Q.card := hQ

end LeanProofs.GowersSzemeredi
