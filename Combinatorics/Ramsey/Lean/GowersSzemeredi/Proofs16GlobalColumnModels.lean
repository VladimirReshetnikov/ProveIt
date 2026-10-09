import GowersSzemeredi.Proofs16FixedColumnWordFamilies
import GowersSzemeredi.Proofs16ColumnModelDomain
import GowersSzemeredi.Proofs16GlobalColumnWordIdentities

/-! A uniformly bounded list of local models in each alternating-value fibre,
constructed directly from the original dense bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnAnchorFibre {N : Nat} [NeZero N] (P : Finset (ZMod N)) (k : Nat) (c : ZMod N) :
    Finset (ColumnAnchorTuple N k) :=
  Finset.univ.filter (fun a => (∀ x ∈ columnAnchorList a, x ∈ P) ∧ columnAnchorEval id (columnAnchorList a) = c)

def globalColumnModelRadius (alpha : Real) (k : Nat) : Real :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d)
    (globalColumnIdentityRadius alpha) (globalColumnWordIdentityRadius alpha k)

def globalColumnModelModulusBound (alpha : Real) (k : Nat) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  max (globalColumnWordIdentityModulusBound alpha k)
    (refinementKernelCap (2*(k+1)*d) (3*(k+1)*d)
      (globalColumnIdentityRadius alpha) (globalColumnWordIdentityRadius alpha k) + 1)

/-- All anchor lists in each fixed-value fibre admit one of at most
`1 / globalColumnWordDensity alpha k` local map models. -/
theorem global_column_models {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (k : Nat) (hN : globalColumnModelModulusBound alpha k ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let r := globalColumnRichnessRadius alpha
    let delta := globalColumnWordDensity alpha k
    let s := globalColumnModelRadius alpha k
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ B ⊆ X ∧ P ⊆ B ∧
      globalColumnVertexDensity alpha*N/2 ≤ (P.card : Real) ∧ 0 < delta ∧ 0 < s ∧
      (∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
        delta*(N : Real)^(3*k+2) ≤ (fixedColumnWordRepresentations B T L r a).card) ∧
      (∀ c : ZMod N, ∃ J ⊆ columnAnchorFibre P k c, (J.card : Real)*delta ≤ 1 ∧
        ∃ Gamma : Finset (ZMod N), Gamma.card ≤ J.card*(k+1)*d ∧
          (Gamma.card : Real)*delta ≤ (k+1)*d ∧
          (∀ j ∈ J, IsFreimanLinearOn (bohr Gamma rho)
            (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList j)) ∧
            columnAnchorEval (fun x => L x 0) (columnAnchorList j) = 0) ∧
          (∀ a ∈ columnAnchorFibre P k c, ∃ j ∈ J,
            ColumnListIdentity T L s (columnAnchorList a) (columnAnchorList j) ∧
            ∀ y ∈ bohr Gamma s, (∀ x ∈ columnAnchorList a, y ∈ bohr (T x) s) →
              columnAnchorEval (fun x => L x y) (columnAnchorList a) =
                columnAnchorEval (fun x => L x y) (columnAnchorList j))) := by
  have hNword : globalColumnWordIdentityModulusBound alpha k ≤ N := (le_max_left _ _).trans hN
  have hNker : refinementKernelCap (2*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      (3*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      (globalColumnIdentityRadius alpha) (globalColumnWordIdentityRadius alpha k) < N :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans hN)
  obtain ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,_,hr,_,hdelta,hs,htriple,hwords,hident,hrich⟩ :=
    global_column_word_identities A phi ha ha1 hA hphi k hNword
  have hrho := globalColumnIdentityRadius_pos ha ha1
  have hsle : globalColumnWordIdentityRadius alpha k ≤ globalColumnIdentityRadius alpha :=
    refinementKernelRadius_le_rho _ _ hrho hr
  have hcount : ∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
      globalColumnWordDensity alpha k*(N : Real)^(3*k+2) ≤
        (fixedColumnWordRepresentations B T L (globalColumnRichnessRadius alpha) a).card := by
    intro a haP
    rw [fixedColumnWordRepresentations_card]
    simpa only [columnAnchorList,List.length_ofFn] using hwords a.1 (List.ofFn a.2) haP
  have hspec : ∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
      ∀ w ∈ fixedColumnWordRepresentations B T L (globalColumnRichnessRadius alpha) a,
        (∀ x ∈ columnWordEntries w, x ∈ B) ∧
        columnWordValue w = columnAnchorEval id (columnAnchorList a) ∧
        ColumnListIdentity T L (globalColumnWordIdentityRadius alpha k) (columnAnchorList a) (columnWordEntries w) := by
    intro a haP w hw
    exact fixedColumnWordRepresentations_spec B T L _ _ a
      (hident a.1 (List.ofFn a.2) haP (by simp)) hw
  refine ⟨X,T,L,W,B,P,hsys,hLfull,hW,hT,hL,hzero,hBX,hPB,hP,hdelta k,
    refinementKernelRadius_pos _ _ hrho hs,hcount,?_⟩
  intro c
  have hpack := column_model_packing (columnAnchorFibre P k c) X T L columnAnchorList
    (fixedColumnWordRepresentations B T L (globalColumnRichnessRadius alpha)) c
    hrho hs hsle (hdelta k) hT hL hzero
    (fun a _ => columnAnchorList_length a)
    (fun a ha x hx => hBX (hPB ((Finset.mem_filter.mp ha).2.1 x hx)))
    (fun a ha w hw x hx => hBX ((hspec a (Finset.mem_filter.mp ha).2.1 w hw).1 x hx))
    (fun a ha w hw => (hspec a (Finset.mem_filter.mp ha).2.1 w hw).2.1.trans (Finset.mem_filter.mp ha).2.2)
    (fun a ha => hcount a (Finset.mem_filter.mp ha).2.1)
    (fun a ha w hw => (hspec a (Finset.mem_filter.mp ha).2.1 w hw).2.2) hNker

  obtain ⟨J,hJA,hJ,hcover⟩ := hpack
  let Gamma := columnModelSpectrum T columnAnchorList J
  have hjX : ∀ j ∈ J, ∀ x ∈ columnAnchorList j, x ∈ X :=
    fun j hj x hx => hBX (hPB ((Finset.mem_filter.mp (hJA hj)).2.1 x hx))
  have hGamma : Gamma.card ≤ J.card*(k+1)*columnSpectrumCap (columnEightDensity alpha) :=
    columnModelSpectrum_card_le T columnAnchorList J
      (fun j _ => (columnAnchorList_length j).le) (fun j hj x hx => hT x (hjX j hj x hx))
  have hGammaR : (Gamma.card : Real)*globalColumnWordDensity alpha k ≤
      (k+1)*columnSpectrumCap (columnEightDensity alpha) := by
    have hGR : (Gamma.card : Real) ≤ (J.card : Real)*(k+1)*columnSpectrumCap (columnEightDensity alpha) := by
      exact_mod_cast hGamma
    calc _ ≤ ((J.card : Real)*(k+1)*columnSpectrumCap (columnEightDensity alpha))*globalColumnWordDensity alpha k :=
        mul_le_mul_of_nonneg_right hGR (hdelta k).le
      _ = ((J.card : Real)*globalColumnWordDensity alpha k)*((k+1)*columnSpectrumCap (columnEightDensity alpha)) := by ring
      _ ≤ 1*((k+1)*columnSpectrumCap (columnEightDensity alpha)) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = _ := one_mul _
  refine ⟨J,hJA,hJ,Gamma,hGamma,hGammaR,
    column_models_freiman T L columnAnchorList J _
      (fun j hj x hx => hL x (hjX j hj x hx))
      (fun j hj x hx => hzero x (hjX j hj x hx)),?_⟩
  intro a haF
  obtain ⟨j,hj,hij⟩ := hcover a haF
  refine ⟨j,hj,hij,?_⟩
  intro y hy hya
  exact hij y hya ((mem_columnModelSpectrum_bohr T columnAnchorList J _ y).mp hy j hj)

end LeanProofs.GowersSzemeredi
