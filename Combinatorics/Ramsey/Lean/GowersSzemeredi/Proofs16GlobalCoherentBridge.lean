import GowersSzemeredi.Proofs16PopularCoherentBridge
import GowersSzemeredi.Proofs16GlobalSingleProgression

/-! A finite coherent weak-transitivity system from the original dense
bihomomorphism, under a fully specified modulus threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalCoherentBridgeModulusBound (alpha : Real) (depth power : Nat) (scale : Real) : Nat :=
  max (globalSingleProgressionModulusBound alpha)
    (singleCoherentBridgeModulusBound (globalPopularAnchorTolerance alpha)
      (globalCoherentAnchorDensity alpha) (globalCoherentAnchorRank alpha)
      (globalEvenColumnZeroRadius alpha 4) depth power scale)

theorem global_coherent_bridge_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (depth power : Nat) {scale : Real} (hscale : 0 < scale)
    (hN : globalCoherentBridgeModulusBound alpha depth power scale ≤ N) :
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
      HasPopularCoherentBridgeSystem P Gamma T L
        ((globalEvenColumnZeroDensity alpha 4)^8/4)
        (globalPopularAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalEvenColumnModelRank alpha 4) (columnSpectrumCap (columnEightDensity alpha))
        (globalEvenColumnZeroRadius alpha 4) depth power scale := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,hsingle⟩ :=
    global_single_coherent_progression A phi ha ha1 hA hphi ((le_max_left _ _).trans hN)
  refine ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,?_⟩
  exact hsingle.bridge_system (globalPopularAnchorTolerance_pos ha ha1)
    (globalCoherentAnchorDensity_pos ha ha1) depth power hscale ((le_max_right _ _).trans hN)

end LeanProofs.GowersSzemeredi
