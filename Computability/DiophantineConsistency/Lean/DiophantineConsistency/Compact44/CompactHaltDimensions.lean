import DiophantineConsistency.Compact44.CompactHaltWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHaltDimensions
open DiophantineConsistency
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticTilingWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem dimensions (T : V) :
    2*T+5 ≤ power 581197 (T+1) ∧
    T+2 ≤ power 581197 (T+3) ∧
    4 ≤ power 581197 (T+3) ∧
    power 581197 (T+1)*power 581197 (T+3) = power 581197 ((2*T+3)+1) := by
  have hp : (2:V) ≤ 581197 := by norm_num
  have h3 := succ_le_power hp (T+3)
  refine ⟨?_,?_,?_,?_⟩
  · rw [power_succ]
    calc 2*T+5 ≤ 581197*(T+1) := by
          rw [mul_add,mul_one]
          exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num : (2:V) ≤ 581197) (Arithmetic.zero_le T)) (by norm_num)
      _ ≤ 581197*power 581197 T := mul_le_mul_of_nonneg_left (succ_le_power hp T) (by norm_num : (0:V) ≤ 581197)
  · exact le_trans (by
      rw [show T+3+1=(T+2)+2 by ring]; exact le_add_of_nonneg_right (by positivity)) h3
  · exact le_trans (by
      rw [show T+3+1=T+4 by ring]; exact le_add_of_nonneg_left (Arithmetic.zero_le T)) h3
  · rw [← power_add]; congr 1; ring

theorem controller_bounds (T : V) :
    power 581197 (T+1) ≤ power 581197 (2*T+3) ∧
    2*(590069*581197) < power 581197 (2*T+3) := by
  have hp : (1:V) ≤ 581197 := by norm_num
  have hexp : T+1 ≤ 2*T+3 := by
    calc T+1 ≤ (T+1)+(T+2) := le_add_of_nonneg_right (show (0:V) ≤ T+2 by positivity)
      _ = 2*T+3 := by ring
  have hm : (3:V) ≤ 2*T+3 := by
    simpa only [zero_add] using le_add_of_nonneg_left (show (0:V)≤2*T by positivity)
  refine ⟨power_mono_exponent 581197 (T+1) (2*T+3) hp hexp, ?_⟩
  have h3 : power (581197:V) 3 = 581197*(581197*581197) := by
    rw [show (3:V)=(2:V)+1 by norm_num, power_succ,
      show (2:V)=(1:V)+1 by norm_num, power_succ, power_one]
  calc 2*(590069*581197) < power (581197:V) 3 := by rw [h3]; norm_num
    _ ≤ power 581197 (2*T+3) := power_mono_exponent 581197 3 (2*T+3) hp hm

theorem halt_compact_word_powers (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    (𝚺₁-Function₁ (fun j => CompactTableLookup.rowLookup
      (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j))) ∧
    CompactMarkedTransport.CompactWord
      (fun j => CompactTableLookup.rowLookup
        (ArithmeticTilingBand.word T (power 581197 (T+1)) (power 581197 (T+3)) j))
      (power 581197 (T+1)*power 581197 (T+3)) (power 581197 (T+1)) := by
  obtain ⟨h1,h2,h3,_⟩ := dimensions T
  exact CompactHaltWord.halt_compact_word T _ _ hT h1 h2 h3
#print axioms CompactHaltDimensions.dimensions
#print axioms CompactHaltDimensions.controller_bounds
#print axioms CompactHaltDimensions.halt_compact_word_powers
end CompactHaltDimensions
