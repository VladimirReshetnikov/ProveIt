import ZFCinPA.ValidatorFormulaEncoder222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LeanProofs.ZFCinPA.ValidatorFormulaEncoder222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorFormulaEncoder222 ValidatorEind222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_is_not_valid_truth (F B s : V) :
    ¬IsUFormula ℒₛₑₜ (0 : V) ∧ encode F B s 0=0 ∧ encode F B s (^⊤ : V)=0 :=
  ⟨IsUFormula.not_zero, encode_zero F B s, encode_verum F B s⟩

theorem fixed_false_code (F B s : V) : encode F B s (^⊥ : V)=1 := encode_falsum F B s

theorem coincident_zero_equality (s : V) :
    atom ?[0, (0 : V)∷0∷0, s] 2 0 (^#(0 : V)∷^#(1 : V)∷0)=Eind (0 : V) 0 := by
  simp [atom, ValidatorEnvironmentLabels254.TermLabels.vec,
    ValidatorEnvironmentLabels254.TermLabels.construction]

theorem free_fallback_membership (s : V) :
    atom ?[0, 0, s] 2 1 (^&(0 : V)∷^&(1 : V)∷0)=wel (1 : V) 1 := by
  simp [atom, ValidatorEnvironmentLabels254.TermLabels.vec,
    ValidatorEnvironmentLabels254.TermLabels.construction,
    ValidatorEnvironmentLabels254.freeLabel]

theorem nested_binders (F B s : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode F B s (^∀ (^∀ p))=wal s (wal (s+2) (encode F ((s+2)∷s∷B) (s+2+2) p)) := by
  rw [encode_all F B s hp.all, encode_all F (s∷B) (s+2) hp]

theorem nested_shift (F B s : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    encode F B s (shift ℒₛₑₜ (^∀ (^∀ p)))=
      encode (ValidatorEnvironmentLabels254.tail F) B s (^∀ (^∀ p)) :=
  encode_shift hp.all.all F B s

#print axioms eind_defined
#print axioms encode_graph
#print axioms encode_total_unique
#print axioms encode_of_not_formula
#print axioms encode_rel
#print axioms encode_nrel
#print axioms encode_shift
#print axioms zero_is_not_valid_truth
#print axioms fixed_false_code
#print axioms coincident_zero_equality
#print axioms free_fallback_membership
#print axioms nested_binders
#print axioms nested_shift

end LeanProofs.ZFCinPA.ValidatorFormulaEncoder222Checks
