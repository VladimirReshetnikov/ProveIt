import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorFormulaEncoder222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Represented source NNF negation agrees with numeric implication-to-false
under the actual C222 theorem predicate. The proof is uniform over internal
typed syntax and arbitrary encoder states. Its code induction fixes the
source environment, bounds the varying encoder state by its one-step
successor and uses the bounded Σ₁ order induction of IΣ₁. No freshness,
stack length, primitive equality identification, source-axiom interpretation
or closed consistency reduction is supplied or asserted. R2Neg is a proof guide only, not an import. -/
namespace LeanProofs.ZFCinPA.ValidatorSourceNegation222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorRelationalCore222 (compose contrapose_of double_neg_intro double_neg_elim all_mono)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two actual checker implications, not a semantic equivalence premise. -/
def CodeIff (a b : V) : Prop := CProv (wim a b) ∧ CProv (wim b a)
abbrev codeNeg (a : V) : V := wim a 1

def NegEq (F B s p : V) : Prop :=
  CodeIff (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p))

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "h1" => (ValidatorImplicationContext.h1 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
local notation "ded2" => (ValidatorImplicationContext.ded2 CProv cProv_classical)
private lemma self_imp (a : V) : CProv (wim a a) := ded1 h0

theorem codeIff_refl (a : V) : CodeIff a a := ⟨self_imp a, self_imp a⟩
theorem codeIff_symm {a b : V} (h : CodeIff a b) : CodeIff b a := ⟨h.2,h.1⟩
theorem codeIff_trans {a b c : V} (h₁ : CodeIff a b) (h₂ : CodeIff b c) :
    CodeIff a c := ⟨compose h₁.1 h₂.1, compose h₂.2 h₁.2⟩

/-- The antecedent implication is reversed in each direction. -/
theorem codeIff_imp {a a' b b' : V} (ha : CodeIff a a') (hb : CodeIff b b') :
    CodeIff (wim a b) (wim a' b') :=
  ⟨ded2 (.mp (.ax hb.1) (.mp h1 (.mp (.ax ha.2) h0))),
   ded2 (.mp (.ax hb.2) (.mp h1 (.mp (.ax ha.1) h0)))⟩

theorem codeIff_neg {a b : V} (h : CodeIff a b) :
    CodeIff (codeNeg a) (codeNeg b) := ⟨contrapose_of h.2, contrapose_of h.1⟩
theorem codeIff_all (i : V) {a b : V} (h : CodeIff a b) :
    CodeIff (wal i a) (wal i b) := ⟨all_mono i h.1, all_mono i h.2⟩
theorem codeIff_doubleNeg (a : V) : CodeIff a (codeNeg (codeNeg a)) :=
  ⟨double_neg_intro a, double_neg_elim a⟩
theorem codeIff_doubleNeg_right {a b : V} (h : CodeIff a b) :
    CodeIff a (codeNeg (codeNeg b)) := codeIff_trans h (codeIff_doubleNeg b)
theorem codeIff_neg_swap {a b : V} (h : CodeIff a (codeNeg b)) :
    CodeIff (codeNeg a) b :=
  codeIff_trans (codeIff_neg h) (codeIff_symm (codeIff_doubleNeg b))

private theorem and_case {a b p q : V}
    (ha : CodeIff a (codeNeg p)) (hb : CodeIff b (codeNeg q)) :
    CodeIff (wim (codeNeg a) b) (codeNeg (codeNeg (wim p (codeNeg q)))) :=
  codeIff_doubleNeg_right (codeIff_imp (codeIff_neg_swap ha) hb)

private theorem or_case {a b p q : V}
    (ha : CodeIff a (codeNeg p)) (hb : CodeIff b (codeNeg q)) :
    CodeIff (codeNeg (wim a (codeNeg b))) (codeNeg (wim (codeNeg p) q)) :=
  codeIff_neg (codeIff_imp ha (codeIff_neg_swap hb))

/-! The source environment `F` is fixed outside the induction. The order
variable is the formula code; the arity, binder stack and stream are bounded
by their one-step successors `n+1`, `s∷B` and `s+2`, which dominate every
recursive call. The invariant is then Σ₁ and the bounded order induction of
IΣ₁ applies. -/
private instance cProv_sigma1 : 𝚺₁-Predicate[V] CProv := cProv_definable
private instance encode_sigma1 : 𝚺₁-Function₄[V] encode := encode_defined.to_definable
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀

private theorem negEq_sigma1 (F : V) : 𝚺₁-Relation₄[V]
    (fun p n B s => IsSemiformula ℒₛₑₜ n p → NegEq F B s p) := by
  unfold NegEq CodeIff codeNeg
  definability

/-- Both actual C222 implications for every typed internal source formula.
The environment and binder state are arbitrary; no freshness or size
constraint on either environment is needed. -/
theorem encode_neg {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) : NegEq F B s p := by
  have hfy : 𝚺₁-Function₄[V] (fun _ n _ _ => n + 1) := by definability
  have hfz : 𝚺₁-Function₄[V] (fun _ _ B s => s ∷ B) := by definability
  have hfw : 𝚺₁-Function₄[V] (fun _ _ _ s => s + 2) := by definability
  have hnB : ∀ B s : V, B ≤ s ∷ B := fun B s => (lt_adjoin' s B).le
  have main : ∀ p n B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p := by
    apply bounded_all_sigma1_order_induction₃ hfy hfz hfw (negEq_sigma1 F)
    intro p n B s ih htyped
    rcases IsSemiformula.case_iff.mp htyped with
      (⟨k,R,v,hr,hv,rfl⟩ | ⟨k,R,v,hr,hv,rfl⟩ | rfl | rfl |
        ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
    · rw [NegEq, neg_rel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
        encode_rel F B s hr hv.isUTerm]
      exact codeIff_refl _
    · rw [NegEq, neg_nrel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
        encode_rel F B s hr hv.isUTerm]
      exact codeIff_doubleNeg _
    · simp only [NegEq, neg_verum, encode_verum, encode_falsum]
      exact ⟨cProv_ex_falso _, ded1 (.mp h0 (.ax cProv_truth))⟩
    · simp only [NegEq, neg_falsum, encode_verum, encode_falsum]
      exact ⟨cProv_mp (cProv_k _ _) (self_imp 1), cProv_mp (cProv_k _ _) cProv_truth⟩
    · have ihp := ih p (by simp) n (by simp) B (hnB B s) s (by simp) hp
      have ihq := ih q (by simp) n (by simp) B (hnB B s) s (by simp) hq
      rw [NegEq, neg_and hp.isUFormula hq.isUFormula,
        encode_or F B s hp.isUFormula.neg hq.isUFormula.neg,
        encode_and F B s hp.isUFormula hq.isUFormula]
      exact and_case ihp ihq
    · have ihp := ih p (by simp) n (by simp) B (hnB B s) s (by simp) hp
      have ihq := ih q (by simp) n (by simp) B (hnB B s) s (by simp) hq
      rw [NegEq, neg_or hp.isUFormula hq.isUFormula,
        encode_and F B s hp.isUFormula.neg hq.isUFormula.neg,
        encode_or F B s hp.isUFormula hq.isUFormula]
      exact or_case ihp ihq
    · have ihp := ih p (by simp) (n+1) le_rfl (s∷B) le_rfl (s+2) le_rfl hp
      rw [NegEq, neg_all hp.isUFormula, encode_exs F B s hp.isUFormula.neg,
        encode_all F B s hp.isUFormula]
      exact codeIff_neg (codeIff_all s (codeIff_neg_swap ihp))
    · have ihp := ih p (by simp) (n+1) le_rfl (s∷B) le_rfl (s+2) le_rfl hp
      rw [NegEq, neg_ex hp.isUFormula, encode_all F B s hp.isUFormula.neg,
        encode_exs F B s hp.isUFormula]
      exact codeIff_doubleNeg_right (codeIff_all s ihp)
  exact main p n B s hp

theorem encode_neg_forward {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p))) :=
  (encode_neg hp F B s).1
theorem encode_neg_backward {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (codeNeg (encode F B s p)) (encode F B s (Bootstrapping.neg ℒₛₑₜ p))) :=
  (encode_neg hp F B s).2

theorem encode_neg_witnesses {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    ∃ d e : V,
      ArithmeticHistory222.value d =
        wim (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) (codeNeg (encode F B s p)) + 1 ∧
      ArithmeticHistory222.value e =
        wim (codeNeg (encode F B s p)) (encode F B s (Bootstrapping.neg ℒₛₑₜ p)) + 1 := by
  obtain ⟨⟨d,hd⟩,⟨e,he⟩⟩ := encode_neg hp F B s
  exact ⟨d,e,hd,he⟩

end LeanProofs.ZFCinPA.ValidatorSourceNegation222
