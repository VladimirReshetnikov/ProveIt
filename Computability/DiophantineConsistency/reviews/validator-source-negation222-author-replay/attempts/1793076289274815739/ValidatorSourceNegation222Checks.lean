import ZFCinPA.ValidatorSourceNegation222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSourceNegation222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222 ValidatorSourceNegation222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

theorem equality_colliding_labels (s : V) :
    NegEq (0 : V) ?[(0 : V),0] s (^rel 2 0 ?[^#(0 : V),^#(1 : V)]) :=
  encode_neg (n := (2 : V)) (by simp) _ _ _

theorem membership_fallback_labels (s : V) :
    NegEq (0 : V) 0 s (^rel 2 1 ?[^&(0 : V),^&(1 : V)]) :=
  encode_neg (n := (0 : V)) (by simp) _ _ _

theorem negated_equality (F B s : V) :
    NegEq F B s (^nrel 2 0 ?[^&(0 : V),^&(1 : V)]) :=
  encode_neg (n := (0 : V)) (by simp) _ _ _

theorem truth_case (F B s : V) : CodeIff (1 : V) (codeNeg (0 : V)) := by
  simpa [NegEq] using encode_neg (n := (0 : V)) (p := (^⊤ : V)) (by simp) F B s

theorem falsity_case (F B s : V) : CodeIff (0 : V) (codeNeg (1 : V)) := by
  simpa [NegEq] using encode_neg (n := (0 : V)) (p := (^⊥ : V)) (by simp) F B s

theorem double_source_negation {n p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (F B s : V) : CodeIff
      (encode F B s (Bootstrapping.neg ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ p)))
      (encode F B s p) :=
  codeIff_trans (encode_neg hp.neg F B s)
    (codeIff_trans (codeIff_neg (encode_neg hp F B s))
      (codeIff_symm (codeIff_doubleNeg _)))

theorem nested_alternation {n p : V} (hp : IsSemiformula ℒₛₑₜ (n+1+1) p)
    (F B s : V) : NegEq F B s (^∀ (^∃ p)) :=
  encode_neg (n := n) (by simpa using hp) F B s

theorem literal_nested_state {p : V} (hp : IsUFormula ℒₛₑₜ p) (F B s : V) :
    encode F B s (^∀ (^∃ p)) =
      wal s (codeNeg (wal (s+2) (codeNeg (encode F ((s+2)∷s∷B) (s+2+2) p)))) := by
  rw [encode_all F B s (by simpa using hp), encode_exs F (s∷B) (s+2) hp]

theorem malformed_zero_excluded (n F B s : V) :
    ¬IsSemiformula ℒₛₑₜ n (0 : V) ∧ encode F B s (0 : V)=0 :=
  ⟨fun h => IsUFormula.not_zero h.isUFormula, encode_zero F B s⟩

#print axioms codeIff_imp
#print axioms codeIff_all
#print axioms codeIff_neg_swap
#print axioms encode_neg
#print axioms encode_neg_forward
#print axioms encode_neg_backward
#print axioms encode_neg_witnesses
#print axioms equality_colliding_labels
#print axioms membership_fallback_labels
#print axioms negated_equality
#print axioms truth_case
#print axioms falsity_case
#print axioms double_source_negation
#print axioms nested_alternation
#print axioms literal_nested_state
#print axioms malformed_zero_excluded

end LeanProofs.ZFCinPA.ValidatorSourceNegation222Checks
