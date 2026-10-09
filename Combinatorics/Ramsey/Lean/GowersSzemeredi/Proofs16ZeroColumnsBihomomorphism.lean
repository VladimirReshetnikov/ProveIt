import GowersSzemeredi.Proofs16GlobalZeroColumnCore
import GowersSzemeredi.Proofs16ColumnBohrDomainDensity

/-! Convert zero column relations into a Freiman bihomomorphism by
including the common frequencies in every column spectrum. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Zero alternating quadruples and columnwise Freiman linearity give
both directional identities on the common restricted domain. -/
theorem zero_columns_bihomomorphism {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {s rho : Real} (hs : s ≤ rho)
    (hL : ∀ x ∈ P, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hquad : ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ P) → q 0-q 1+q 2-q 3 = 0 →
      ∀ y ∈ bohr Gamma s, (∀ i, y ∈ bohr (T (q i)) s) → columnQuadValue L q y = 0) :
    IsEBihomomorphism (columnBohrDomain P (fun x => Gamma ∪ T x) s)
      (fun p => L p.1 p.2) {0} := by
  have hmem (x y : ZMod N) (h : (x,y) ∈ columnBohrDomain P (fun x => Gamma ∪ T x) s) :
      x ∈ P ∧ y ∈ bohr Gamma s ∧ y ∈ bohr (T x) s := by
    simpa only [columnBohrDomain,Finset.mem_filter,Finset.mem_univ,true_and,
      bohr_union,Finset.mem_inter] using h
  constructor
  · intro a b c d y heq ha hb hc hd
    obtain ⟨haP,hyG,hya⟩ := hmem a y ha
    obtain ⟨hbP,_,hyb⟩ := hmem b y hb
    obtain ⟨hcP,_,hyc⟩ := hmem c y hc
    obtain ⟨hdP,_,hyd⟩ := hmem d y hd
    have hq : ∀ i, (![a,c,b,d] : Fin 4 → ZMod N) i ∈ P := by
      intro i; fin_cases i <;> assumption
    have hyq : ∀ i, y ∈ bohr (T ((![a,c,b,d] : Fin 4 → ZMod N) i)) s := by
      intro i; fin_cases i <;> assumption
    have he : a-c+b-d = 0 := by linear_combination heq
    have h := hquad ![a,c,b,d] hq he y hyG hyq
    change L a y+L b y-L c y-L d y ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    dsimp [columnQuadValue] at h
    linear_combination h
  · intro x a b c d heq ha hb hc hd
    have h := hL x (hmem x a ha).1 a b c d
      (bohr_mono_radius _ hs (hmem x a ha).2.2)
      (bohr_mono_radius _ hs (hmem x b hb).2.2)
      (bohr_mono_radius _ hs (hmem x c hc).2.2)
      (bohr_mono_radius _ hs (hmem x d hd).2.2) heq
    change L x a+L x b-L x c-L x d ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    linear_combination h

/-- An explicit dense column core with bounded enlarged spectra and an
actual Freiman bihomomorphism, retaining the original witness system. -/
theorem global_column_core_bihomomorphism {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnZeroModulusBound alpha ≤ N) :
    ∃ (X P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧ P ⊆ X ∧ P.Nonempty ∧
      globalColumnZeroDensity alpha*N ≤ (P.card : Real) ∧
      (∀ x ∈ P, (Gamma ∪ T x).card ≤ globalColumnModelRank alpha +
        columnSpectrumCap (columnEightDensity alpha)) ∧
      (∀ x ∈ P, L x 0 = 0) ∧
      IsEBihomomorphism (columnBohrDomain P (fun x => Gamma ∪ T x) (globalColumnZeroRadius alpha))
        (fun p => L p.1 p.2) {0} ∧
      globalColumnZeroDensity alpha*(N : Real)^2 ≤
        (refinementCells (globalColumnZeroRadius alpha) : Real)^
          (globalColumnModelRank alpha+columnSpectrumCap (columnEightDensity alpha))*
          (columnBohrDomain P (fun x => Gamma ∪ T x) (globalColumnZeroRadius alpha)).card := by
  obtain ⟨X,T,L,W,P,Gamma,hsys,hW,hT,hL,hzero,hPX,hPne,hP,hG,hquad⟩ :=
    global_zero_column_core A phi ha ha1 hA hphi hN
  have hST : ∀ x ∈ P, (Gamma ∪ T x).card ≤ globalColumnModelRank alpha+
      columnSpectrumCap (columnEightDensity alpha) := by
    intro x hx
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hG (hT x (hPX hx)))
  refine ⟨X,P,Gamma,T,L,W,hsys,hW,hPX,hPne,hP,hST,fun x hx => hzero x (hPX hx),?_,?_⟩
  · exact zero_columns_bihomomorphism P Gamma T L (globalColumnZeroRadius_le ha ha1)
      (fun x hx => hL x (hPX hx)) hquad
  · have hs := globalColumnZeroRadius_pos ha ha1
    let Q := refinementCells (globalColumnZeroRadius alpha)
    have hQpos : 0 < Q := Nat.ceil_pos.mpr (by positivity)
    letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
    have hQ : 1 ≤ globalColumnZeroRadius alpha*Q := by
      have hceil : 1/globalColumnZeroRadius alpha ≤ (Q : Real) := Nat.le_ceil _
      simpa only [mul_comm] using (div_le_iff₀ hs).mp hceil
    exact columnBohrDomain_density_lower P (fun x => Gamma ∪ T x) hQ hST hP

end LeanProofs.GowersSzemeredi
