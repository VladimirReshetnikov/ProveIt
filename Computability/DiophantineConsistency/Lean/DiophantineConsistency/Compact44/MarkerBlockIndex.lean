import DiophantineConsistency.Compact44.FixedGraphFieldMarkers
import DiophantineConsistency.Compact44.BlockOrbit
import DiophantineConsistency.Compact44.TemporalSafeCyclic
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace MarkerBlockIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem previous (N g : V) (hN : 0<N) (hg : g<N) :
    cyc (8807*N) (8807*g+1073) 8849 = 8807*(cyc N g 1)+1031 := by
  have hn : 0<8807*N := mul_pos (by norm_num) hN
  have hs : 1%N<N := mod_lt _ hN
  have hmod : (8807:V)%(8807*N)=8807*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8807:V)) (a:=(1:V)) (b:=N) (by norm_num) hN)
  calc
    _ = cyc (8807*N) (cyc (8807*N) (8807*g+1073) 42) 8807 := by
      rw [TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8807*N) (8807*g+1031) 8807 := by
      rw [BlockCyclicIndex.reflected N g 1073 42 hg (by norm_num) (by norm_num)]
      rw [show (1073:V)-42=1031 from (eq_tsub_of_add_eq (by norm_num : (1031:V)+42=1073)).symm]
    _ = cyc (8807*N) (8807*g+1031) (8807*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8807*(cyc N g (1%N))+1031 := BlockCyclicIndex.shift N g (1%N) 1031 hg hs (by norm_num)
    _ = 8807*(cyc N g 1)+1031 := by rw [cyc_mod _ _ _ hN]

theorem marker (N C g : V) (hN : 0<N) (hg : g<N)
    (heq : ∀ k<8807*N, k%8807=1073 →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849)) :
    dig 67 C (8807*g+1011)=dig 67 C (8807*(cyc N g 1)+1031) := by
  have hi := BlockCyclicIndex.index N g 1073 hg (by norm_num)
  have he := heq _ hi.1 hi.2
  rw [BlockCyclicIndex.reflected N g 1073 62 hg (by norm_num) (by norm_num),previous N g hN hg] at he
  rw [show (1073:V)-62=1011 from (eq_tsub_of_add_eq (by norm_num : (1011:V)+62=1073)).symm] at he
  exact he
#print axioms MarkerBlockIndex.previous
#print axioms MarkerBlockIndex.marker
end MarkerBlockIndex
