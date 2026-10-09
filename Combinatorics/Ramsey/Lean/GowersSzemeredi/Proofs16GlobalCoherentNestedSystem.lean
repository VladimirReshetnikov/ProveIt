import GowersSzemeredi.Proofs16PopularCoherentNestedSystem
import GowersSzemeredi.Proofs16GlobalCoherentBridge
import GowersSzemeredi.Proofs16CoherentNestedLayers
import GowersSzemeredi.Proofs16CoherentNestedGraphProfile

/-! Construct dense compatible word families from the original bihomomorphism,
retaining its actual column and popular anchor witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalCoherentNestedModulusBound (alpha : Real) (K J : Nat) : Nat :=
  max (globalCoherentBridgeModulusBound alpha (coherentNestedBridgeDepth K J) (coherentNestedBridgePower K J) (coherentNestedBridgeScale K J)) 3

theorem global_coherent_nested_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (K J : Nat) (hN : globalCoherentNestedModulusBound alpha K J ≤ N) :
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
      HasPopularCoherentNestedSystem P Gamma T L
        ((globalEvenColumnZeroDensity alpha 4)^8/4)
        (globalPopularAnchorTolerance alpha) (globalCoherentAnchorDensity alpha)
        (globalEvenColumnModelRank alpha 4) (columnSpectrumCap (columnEightDensity alpha))
        (globalEvenColumnZeroRadius alpha 4) K J := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,hbridge⟩ :=
    global_coherent_bridge_system A phi ha ha1 hA hphi (coherentNestedBridgeDepth K J) (coherentNestedBridgePower K J) (coherentNestedBridgeScale_pos K J)
      ((le_max_left _ _).trans hN)
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  exact ⟨X,P,Gamma,T,L,W,hsys,hL,hW,hT,hzero,hPX,hP,hG,hrel,
    hbridge.nested_system (by omega)⟩

end LeanProofs.GowersSzemeredi
