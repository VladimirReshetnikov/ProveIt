import GowersSzemeredi.Proofs16CoherentProgressionRows

/-! Coherent progression rows from the original dense bihomomorphism.
All column witnesses and even-core relations are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_popular_coherent_progression_rows {N : Nat} [NeZero N] [Fact N.Prime]
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
      HasCoherentProgressionRows
        (popularSupportedHigherArrangements P ((globalEvenColumnZeroDensity alpha 4)^8/4))
        (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
        (globalPopularAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalCoherentAnchorRank alpha) (globalEvenColumnZeroRadius alpha 4) := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,hanchors⟩ :=
    global_popular_coherent_column_anchors A phi ha ha1 hA hphi hN
  refine ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,?_⟩
  exact hanchors.progression_rows (globalCoherentAnchorDensity_pos ha ha1)
    (globalPopularAnchorTolerance_pos ha ha1)
    (coreColumnSpectrum_card_le P Gamma T hG (fun x hx => hT x (hPX hx)))

end LeanProofs.GowersSzemeredi
