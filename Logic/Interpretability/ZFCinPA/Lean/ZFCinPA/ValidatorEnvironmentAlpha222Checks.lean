import ZFCinPA.ValidatorEnvironmentAlpha222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEindContext222 ValidatorAtomicTransport222 ValidatorEnvironmentAlpha222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem malformed_zero (h F B B' s t : V) :
    EqUnder h (encode F B s 0) (encode F B' t 0) :=
  encode_malformed_eq_under h F B B' s t IsUFormula.not_zero

theorem streams_cannot_coincide (s : V) : ¬Apart s s := by
  intro h
  exact h 0 0 rfl

/-- Identical encodings use finite reflexivity, not an impossible Apart premise. -/
theorem same_stream_reflexive (h F B s p : V) :
    EqUnder h (encode F B s p) (encode F B s p) := eqUnder_refl h _

theorem twice_pushed {F B B' s t : V} (h : FreshPair F B B' s t) :
    FreshPair F ((s+2)∷s∷B) ((t+2)∷t∷B') (s+4) (t+4) := by
  have hh := freshPair_next (freshPair_next h)
  simpa only [show (s+2)+2=s+4 by ring,show (t+2)+2=t+4 by ring] using hh

theorem reverse_all_same_context (B B' P Q x y : V)
    (hb : EqUnder (eindContext (x∷B) (y∷B')) P Q)
    (vxh : Vac x (eindContext B B')) (vyh : Vac y (eindContext B B'))
    (vxQ : Vac x Q) (vyP : Vac y P) :
    CProv (wim (eindContext B B') (wim (wal y Q) (wal x P))) :=
  (eqUnder_all_of_cons B B' P Q x y hb vxh vyh vxQ vyP).2

theorem actual_reverse_witness {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    ∃ code : V, ArithmeticHistory222.value code =
      wim (eindContext B B') (wim (encode F B' t p) (encode F B s p))+1 :=
  (encode_alpha_witnesses hp F B B' s t hB hB' hf).2

#print axioms freshPair_next
#print axioms cross_body_vac
#print axioms eqUnder_all_of_cons
#print axioms eqUnder_ex_of_cons
#print axioms encoded_binder_steps
#print axioms encode_eq_under
#print axioms encode_formula_alpha
#print axioms encode_malformed_eq_under
#print axioms encode_alpha_witnesses
#print axioms malformed_zero
#print axioms streams_cannot_coincide
#print axioms same_stream_reflexive
#print axioms twice_pushed
#print axioms reverse_all_same_context
#print axioms actual_reverse_witness
end LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha222Checks
