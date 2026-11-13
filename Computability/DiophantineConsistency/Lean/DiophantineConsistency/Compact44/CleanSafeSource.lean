import DiophantineConsistency.Compact44.CyclicPhaseTransport
import DiophantineConsistency.Compact44.CleanModelSupport
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanSafeSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem safe_source (N C k : V) (hN : 0<N) (hk : k<8807*N) (hsafe : ¬Bad (k%8807))
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hbool : ∀ j<8807*N, j%8807≠1063 → dig 67 C j≤1) :
    dig 67 C k=0 ∧ dig 67 C (cyc (8807*N) k 1)≤1 ∧
      dig 67 C (cyc (8807*N) k 2)≤1 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hp := CleanPhaseNeighbors.model_neighbors (k%8807) (mod_lt _ (by norm_num)) hsafe
  refine ⟨hzero k hk hsafe, ?_, ?_⟩
  · apply hbool _ (cyc_lt hn _ _)
    rw [CyclicPhaseTransport.cyc_period 8807 N k 1 (by norm_num) hN (by norm_num)]
    exact hp.1
  · apply hbool _ (cyc_lt hn _ _)
    rw [CyclicPhaseTransport.cyc_period 8807 N k 2 (by norm_num) hN (by norm_num)]
    exact hp.2

theorem choose_source (N C q k₁ k₂ : V) (hN : 0<N)
    (hk₁ : k₁<8807*N) (hk₂ : k₂<8807*N)
    (hphase₁ : k₁%8807=cyc 8807 4393 q) (hphase₂ : k₂%8807=cyc 8807 5495 q)
    (hzero : ∀ j<8807*N, ¬Bad (j%8807) → dig 67 C j=0)
    (hbool : ∀ j<8807*N, j%8807≠1063 → dig 67 C j≤1) :
    ∃ k, (k=k₁ ∨ k=k₂) ∧ k<8807*N ∧ dig 67 C k=0 ∧
      dig 67 C (cyc (8807*N) k 1)≤1 ∧ dig 67 C (cyc (8807*N) k 2)≤1 := by
  rcases CleanTargetPhase.target_choice q with h₁ | h₂
  · have hs : ¬Bad (k₁%8807) := by rw [hphase₁]; exact h₁
    exact ⟨k₁,Or.inl rfl,hk₁,safe_source N C k₁ hN hk₁ hs hzero hbool⟩
  · have hs : ¬Bad (k₂%8807) := by rw [hphase₂]; exact h₂
    exact ⟨k₂,Or.inr rfl,hk₂,safe_source N C k₂ hN hk₂ hs hzero hbool⟩
#print axioms CleanSafeSource.safe_source
#print axioms CleanSafeSource.choose_source
end CleanSafeSource
