import ZFCinPA.ValidatorExistentialRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorExistentialRules222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorEnvironmentAlpha222 ValidatorEnvironmentSubstitution222
open ValidatorExistentialRules222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

theorem fallback_one {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (index s : V) (hs : StreamFree s (0 : V)) :
    CProv (wim (encode 0 (1∷0) s p) (encode 0 0 s (^∃ p))) := by
  have h := ex_term_imp hp (show IsTerm ℒₛₑₜ (^&index : V) by simp) 0 s hs
  simpa only [encode_substs1_fvar,ValidatorEnvironmentLabels254.freeLabel_nil] using h

theorem stored_zero {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (s : V) (hs : StreamFree s (0∷0 : V)) :
    CProv (wim (encode (0∷0) (0∷0) s p) (encode (0∷0) 0 s (^∃ p))) := by
  have h := ex_term_imp hp (show IsTerm ℒₛₑₜ (^&0 : V) by simp) (0∷0) s hs
  simpa only [encode_substs1_fvar,ValidatorEnvironmentLabels254.freeLabel_cons_zero] using h

theorem repeated_zero {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (s : V) (hs : StreamFree s (0∷0∷0 : V)) :
    CProv (wim (encode (0∷0∷0) (0∷0) s p) (encode (0∷0∷0) 0 s (^∃ p))) := by
  have h := ex_term_imp hp (show IsTerm ℒₛₑₜ (^&1 : V) by simp) (0∷0∷0) s hs
  simpa [encode_substs1_fvar] using h

theorem nested_binder {p t : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s (substs1 ℒₛₑₜ t (^∀ p)))
      (encode F 0 s (^∃ (^∀ p)))) :=
  ex_term_imp (show IsSemiformula ℒₛₑₜ 1 (^∀ p) by simpa using hp) ht F s hs

theorem actual_implication_witness {p t : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F) :
    ∃ code : V, ArithmeticHistory222.value code=
      wim (encode F 0 s (substs1 ℒₛₑₜ t p)) (encode F 0 s (^∃ p))+1 :=
  ex_term_imp hp ht F s hs

theorem arbitrary_hypothesis {p t H : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (ht : IsTerm ℒₛₑₜ t) (F s : V) (hs : StreamFree s F)
    (h : CProv (wim H (encode F 0 s (substs1 ℒₛₑₜ t p)))) :
    ∃ code : V, ArithmeticHistory222.value code=wim H (encode F 0 s (^∃ p))+1 :=
  ex_term_rule_under hp ht F s H hs h

#print axioms ex_intro_relational
#print axioms term_fresh_pair
#print axioms instance_vac
#print axioms instance_primitive_transport
#print axioms ex_term_imp
#print axioms ex_term_rule
#print axioms ex_term_rule_under
#print axioms fallback_one
#print axioms stored_zero
#print axioms repeated_zero
#print axioms nested_binder
#print axioms actual_implication_witness
#print axioms arbitrary_hypothesis
end LeanProofs.ZFCinPA.ValidatorExistentialRules222Checks
