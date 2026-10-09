import GowersSzemeredi.Proofs16GlobalCoherentAnchorParameters

/-! Coherent global anchors constructed from the original dense Freiman
bihomomorphism, with no compatibility, relation-failure, or arrangement
mass assumptions. The original column witnesses are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_coherent_column_anchors {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalCoherentAnchorModulusBound alpha ≤ N) :
    ∃ (X P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ columnSpectrumCap (columnEightDensity alpha)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧ P ⊆ X ∧
      globalEvenColumnZeroDensity alpha 4*(N : Real) ≤ P.card ∧
      Gamma.card ≤ globalEvenColumnModelRank alpha 4 ∧
      EvenColumnCoreRelations P Gamma T L (globalEvenColumnZeroRadius alpha 4) 4 ∧
      HasCoherentAnchorSystem P (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
        (globalCoherentAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalCoherentAnchorRank alpha) (globalEvenColumnZeroRadius alpha 4) := by
  have hNcore : globalEvenColumnZeroModulusBound alpha 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨X,T,L,W,P,Gamma,hsys,hLfull,hW,hT,hL,hzero,hPX,hPne,hP,hG,hrel⟩ :=
    global_even_zero_column_core (k := 4) A phi ha ha1 hA hphi hNcore
  refine ⟨X,P,Gamma,T,L,W,hsys,hLfull,hW,hT,hzero,hPX,hP,hG,hrel,?_⟩
  exact coherent_anchor_system_of_even_core P Gamma T L
    (globalEvenColumnZeroRadius_pos ha ha1) (globalEvenColumnZeroRadius_lt_four ha ha1)
    (globalEvenColumnZeroRadius_le ha ha1) (globalEvenColumnZeroDensity_pos ha ha1)
    hP hG (fun x hx => hT x (hPX hx)) (fun x hx => hL x (hPX hx))
    (fun x hx => hzero x (hPX hx)) hrel (globalCoherentAnchorModulusBound_mass ha ha1 hN)

end LeanProofs.GowersSzemeredi
