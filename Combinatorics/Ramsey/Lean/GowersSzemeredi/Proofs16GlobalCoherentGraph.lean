import GowersSzemeredi.Proofs16PopularCoherentGraph
import GowersSzemeredi.Proofs16GlobalSingleProgression

/-! A density-controlled coherent Bohr graph from the original dense
bihomomorphism, under a fully specified modulus threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalCoherentGraphModulusBound (alpha : Real) (power : Nat) (scale : Real) : Nat :=
  max (globalSingleProgressionModulusBound alpha)
    (singleCoherentGraphModulusBound (globalPopularAnchorTolerance alpha)
      (globalCoherentAnchorDensity alpha) (globalCoherentAnchorRank alpha)
      (globalEvenColumnZeroRadius alpha 4) power scale)

theorem global_coherent_density_controlled_graph {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (power : Nat) {scale : Real} (hscale : 0 < scale)
    (hN : globalCoherentGraphModulusBound alpha power scale ≤ N) :
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
      HasPopularCoherentGraph P Gamma T L
        ((globalEvenColumnZeroDensity alpha 4)^8/4)
        (globalPopularAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalEvenColumnModelRank alpha 4) (columnSpectrumCap (columnEightDensity alpha))
        (globalEvenColumnZeroRadius alpha 4) power scale := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,hsingle⟩ :=
    global_single_coherent_progression A phi ha ha1 hA hphi ((le_max_left _ _).trans hN)
  refine ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,?_⟩
  exact hsingle.density_controlled_graph (globalPopularAnchorTolerance_pos ha ha1)
    (globalCoherentAnchorDensity_pos ha ha1) power hscale ((le_max_right _ _).trans hN)

end LeanProofs.GowersSzemeredi
