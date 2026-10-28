import ZFCinPA.ValidatorQuantifierRules222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorQuantifierRules222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222 ValidatorQuantifierRules222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_original_seed (F : V) (hs : StreamFree 0 F) :
    StreamFree 0 (eigen F 0∷F) := (fresh_resources F 0 hs).2.2.1

theorem avoids_fallback (F s : V) (hs : StreamFree s F) : eigen F s≠1 :=
  (fresh_resources F s hs).1.1

theorem extended_stream_safety (F s : V) (hs : StreamFree s F) :
    StreamFree (eigen F s+2) (eigen F s∷F) := (fresh_resources F s hs).2.2.2.1

section
theorem actual_all_witness {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F)
    (h : CProv (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :
    ∃ code : V, ArithmeticHistory222.value code=encode F 0 s (^∀ p)+1 :=
  all_rule hp F s hs h

theorem truth_context {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F)
    (h : CProv (wim 0 (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) :
    CProv (wim 0 (encode F 0 s (^∀ p))) :=
  all_rule_under hp F s 0 hs (vac_truth (eigen F s)) h

theorem source_context_witness {p A : V}
    (hp : IsSemiformula ℒₛₑₜ 1 p) (hA : IsFormula ℒₛₑₜ A)
    (F s : V) (hs : StreamFree s F)
    (h : CProv (wim (neg (encode (eigen F s∷F) 0 s (shift ℒₛₑₜ A)))
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) :
    ∃ code : V, ArithmeticHistory222.value code=
      wim (neg (encode F 0 s A)) (encode F 0 s (^∀ p))+1 :=
  all_rule_under_negated_source hp hA F s hs h
end

#print axioms fresh_resources
#print axioms opened_body_equiv
#print axioms all_opened_equiv
#print axioms ex_opened_equiv
#print axioms all_rule
#print axioms all_rule_under
#print axioms all_rule_under_negated_source
#print axioms zero_original_seed
#print axioms avoids_fallback
#print axioms extended_stream_safety
#print axioms actual_all_witness
#print axioms truth_context
#print axioms source_context_witness
end LeanProofs.ZFCinPA.ValidatorQuantifierRules222Checks
