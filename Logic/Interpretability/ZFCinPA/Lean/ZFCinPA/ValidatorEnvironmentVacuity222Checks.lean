import ZFCinPA.ValidatorEnvironmentVacuity222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorFormulaEncoder222 ValidatorRelationalCore222 ValidatorProvability222
open ValidatorEnvironmentVacuity222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem malformed_zero_without_freshness (F B s z : V) :
    Vac z (encode F B s 0) := encode_malformed_vac F B s z IsUFormula.not_zero

/-- No extra avoidance of Eind's auxiliary label is required. -/
theorem equality_auxiliary_binder (a b : V) :
    Vac (ValidatorEind222.aux a b) (ValidatorEind222.Eind a b) :=
  ValidatorEind222.Eind_vac a b _ (ValidatorEind222.aux_ne a b).1
    (ValidatorEind222.aux_ne a b).2

theorem zero_generalization_label (a b : V) (ha : (0 : V) ≠ a) (hb : (0 : V) ≠ b) :
    Vac (0 : V) (ValidatorEind222.Eind a b) := ValidatorEind222.Eind_vac a b 0 ha hb

theorem repeated_stored_labels (a z : V) (ha : z≠a) : Avoid z (a∷a∷(0 : V)) :=
  avoid_cons (avoid_cons (avoid_nil z) ha) ha

theorem fresh_above_generalization (z s : V) (h : z<s) : StreamAvoid z s := stream_of_lt h

theorem actual_numeric_checker_witness {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s z : V) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z s) :
    ∃ code : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code =
      wim (encode F B s p) (wal z (encode F B s p)) + 1 :=
  encode_vac_witness hp F B s z hlen hF hB hs

#print axioms term_label_avoids
#print axioms atom_vac
#print axioms encode_vac
#print axioms encode_formula_vac
#print axioms encode_vac_witness
#print axioms encode_malformed_vac
#print axioms malformed_zero_without_freshness
#print axioms equality_auxiliary_binder
#print axioms zero_generalization_label
#print axioms repeated_stored_labels
#print axioms actual_numeric_checker_witness

end LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222Checks
