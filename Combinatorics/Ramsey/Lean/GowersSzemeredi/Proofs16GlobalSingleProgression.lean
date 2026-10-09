import GowersSzemeredi.Proofs16SingleProgressionAgreement

/-! A single coherent system with Freiman frequencies on a proper progression,
constructed from the original dense bihomomorphism with explicit losses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalSingleProgressionModulusBound (alpha : Real) : Nat :=
  max (globalCoherentAnchorModulusBound alpha)
    (singleProgressionModulusBound (globalPopularAnchorTolerance alpha)
      (globalCoherentAnchorDensity alpha) (globalCoherentAnchorRank alpha)
      (globalEvenColumnZeroRadius alpha 4))

theorem global_single_coherent_progression {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalSingleProgressionModulusBound alpha ≤ N) :
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
      HasPopularSingleCoherentProgression P Gamma T L
        ((globalEvenColumnZeroDensity alpha 4)^8/4)
        (globalPopularAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalEvenColumnModelRank alpha 4) (columnSpectrumCap (columnEightDensity alpha))
        (globalEvenColumnZeroRadius alpha 4) := by
  have hNcore : globalCoherentAnchorModulusBound alpha ≤ N := (le_max_left _ _).trans hN
  have hNsingle : singleProgressionModulusBound (globalPopularAnchorTolerance alpha)
      (globalCoherentAnchorDensity alpha) (globalCoherentAnchorRank alpha)
      (globalEvenColumnZeroRadius alpha 4) ≤ N := (le_max_right _ _).trans hN
  obtain ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,hrows⟩ :=
    global_popular_coherent_progression_rows A phi ha ha1 hA hphi hNcore
  have hsingle := hrows.single_system (singleProgressionModulusBound_mass
    (globalPopularAnchorTolerance_pos ha ha1) (globalCoherentAnchorDensity_pos ha ha1) hNsingle)
  refine ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,?_⟩
  exact hsingle.with_popular_agreement (globalEvenColumnZeroRadius_pos ha ha1)
    ((globalEvenColumnZeroRadius_le ha ha1).trans (globalColumnIdentityRadius_le ha ha1))
    hG (fun x hx => hT x (hPX hx)) (fun x hx => hL x (hPX hx))
    (fun x hx => hzero x (hPX hx)) hrel

end LeanProofs.GowersSzemeredi
