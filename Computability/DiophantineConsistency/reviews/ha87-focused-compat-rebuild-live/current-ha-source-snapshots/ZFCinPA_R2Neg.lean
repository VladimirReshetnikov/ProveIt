import ZFCinPA.R2Ctx

set_option autoImplicit false
noncomputable section

/-!
# R2: Foundation negation versus validator negation

Foundation's `neg` is the negation-normal-form dual (it swaps `⋏`/`⋎`,
`∀`/`∃` and atoms with negated atoms), while the validator negates by
`a ↦ a → ⊥`. For every internal semiformula and every encoder state,

`CProv (enc (neg p) → ¬enc p)` and `CProv (¬enc p → enc (neg p))`

(`encode_neg`), by `Π₂` induction on the code (`IΣ₂`), with every
propositional step an instance of a checked tautology (`taut`, Kalmár's
completeness lemma) and the quantifier steps by monotonicity of `∀`.
-/

namespace LeanProofs.ZFCinPA.R2Neg

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.R2Ctx
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Tautologies -/

/-- Substitution from a finite list. -/
def sig (l : List V) : ℕ → V := fun n ↦ l.getD n 0

/-- Every substitution instance of a bounded tautology is a validator theorem. -/
lemma taut (f : Kalmar.PF) (n : ℕ) (hb : f.Bounded n) (ht : f.Tautology) (σ : ℕ → V) :
    CProv (f.eval wim 1 σ) :=
  Kalmar.tautology_complete cProv_classical f n hb ht σ

open Kalmar.PF in
/-- `(x ↔ y)`-style equivalences as two implications. -/
def Iff2 (a b : V) : Prop := CProv (wim a b) ∧ CProv (wim b a)

/-- The negation of `p` as a validator code. -/
abbrev vneg (a : V) : V := wim a 1

/-- The equivalence claimed for one formula. -/
def NegEq (F B s p : V) : Prop :=
  CProv (wim (encode F B s (neg ℒₛₑₜ p)) (vneg (encode F B s p))) ∧
  CProv (wim (vneg (encode F B s p)) (encode F B s (neg ℒₛₑₜ p)))

section Taut

open Kalmar.PF

local notation "⊥'" => Kalmar.PF.bot
local infixr:60 " ⟹ " => Kalmar.PF.imp
local notation "x0" => Kalmar.PF.var 0
local notation "x1" => Kalmar.PF.var 1
local notation "x2" => Kalmar.PF.var 2
local notation "x3" => Kalmar.PF.var 3

/-- `a ↔ ¬p`, `b ↔ ¬q` give `((a → ⊥) → b) ↔ ¬¬(p → ¬q)`. -/
lemma and_case {a b p q : V}
    (ha : Iff2 a (vneg p)) (hb : Iff2 b (vneg q)) :
    Iff2 (wim (vneg a) b) (vneg (vneg (wim p (vneg q)))) := by
  constructor
  · have t := taut ((x0 ⟹ (x2 ⟹ ⊥')) ⟹ ((x2 ⟹ ⊥') ⟹ x0) ⟹ (x1 ⟹ (x3 ⟹ ⊥')) ⟹
      ((x3 ⟹ ⊥') ⟹ x1) ⟹ (((x0 ⟹ ⊥') ⟹ x1) ⟹ (((x2 ⟹ (x3 ⟹ ⊥')) ⟹ ⊥') ⟹ ⊥'))) 4
      (by repeat' (first | exact trivial | decide | constructor)) (by
        intro v; simp only [truth]
        generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2; generalize v 3 = a3
        revert a0 a1 a2 a3; decide) (sig [a, b, p, q])
    simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
    exact cProv_mp (cProv_mp (cProv_mp (cProv_mp t ha.1) ha.2) hb.1) hb.2
  · have t := taut ((x0 ⟹ (x2 ⟹ ⊥')) ⟹ ((x2 ⟹ ⊥') ⟹ x0) ⟹ (x1 ⟹ (x3 ⟹ ⊥')) ⟹
      ((x3 ⟹ ⊥') ⟹ x1) ⟹ ((((x2 ⟹ (x3 ⟹ ⊥')) ⟹ ⊥') ⟹ ⊥') ⟹ ((x0 ⟹ ⊥') ⟹ x1))) 4
      (by repeat' (first | exact trivial | decide | constructor)) (by
        intro v; simp only [truth]
        generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2; generalize v 3 = a3
        revert a0 a1 a2 a3; decide) (sig [a, b, p, q])
    simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
    exact cProv_mp (cProv_mp (cProv_mp (cProv_mp t ha.1) ha.2) hb.1) hb.2

/-- `a ↔ ¬p`, `b ↔ ¬q` give `¬(a → ¬b) ↔ ¬((¬p) → q)`. -/
lemma or_case {a b p q : V}
    (ha : Iff2 a (vneg p)) (hb : Iff2 b (vneg q)) :
    Iff2 (vneg (wim a (vneg b))) (vneg (wim (vneg p) q)) := by
  constructor
  · have t := taut ((x0 ⟹ (x2 ⟹ ⊥')) ⟹ ((x2 ⟹ ⊥') ⟹ x0) ⟹ (x1 ⟹ (x3 ⟹ ⊥')) ⟹
      ((x3 ⟹ ⊥') ⟹ x1) ⟹ (((x0 ⟹ (x1 ⟹ ⊥')) ⟹ ⊥') ⟹ (((x2 ⟹ ⊥') ⟹ x3) ⟹ ⊥'))) 4
      (by repeat' (first | exact trivial | decide | constructor)) (by
        intro v; simp only [truth]
        generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2; generalize v 3 = a3
        revert a0 a1 a2 a3; decide) (sig [a, b, p, q])
    simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
    exact cProv_mp (cProv_mp (cProv_mp (cProv_mp t ha.1) ha.2) hb.1) hb.2
  · have t := taut ((x0 ⟹ (x2 ⟹ ⊥')) ⟹ ((x2 ⟹ ⊥') ⟹ x0) ⟹ (x1 ⟹ (x3 ⟹ ⊥')) ⟹
      ((x3 ⟹ ⊥') ⟹ x1) ⟹ ((((x2 ⟹ ⊥') ⟹ x3) ⟹ ⊥') ⟹ ((x0 ⟹ (x1 ⟹ ⊥')) ⟹ ⊥'))) 4
      (by repeat' (first | exact trivial | decide | constructor)) (by
        intro v; simp only [truth]
        generalize v 0 = a0; generalize v 1 = a1; generalize v 2 = a2; generalize v 3 = a3
        revert a0 a1 a2 a3; decide) (sig [a, b, p, q])
    simp only [eval, sig, List.getD_cons_zero, List.getD_cons_succ] at t
    exact cProv_mp (cProv_mp (cProv_mp (cProv_mp t ha.1) ha.2) hb.1) hb.2

/-- `a ↔ b` gives `a ↔ ¬¬b`. -/
lemma dneg_right {a b : V} (h : Iff2 a b) : Iff2 a (vneg (vneg b)) :=
  ⟨R2Ctx.ded1 (.mp (.ax (ValidatorQuantifierCore254.double_neg_intro b)) (.mp (.ax h.1) h0)),
   R2Ctx.ded1 (.mp (.ax h.2) (.mp (.ax (ValidatorQuantifierCore254.double_neg_elim b)) h0))⟩

end Taut

lemma iff2_symm {a b : V} (h : Iff2 a b) : Iff2 b a := ⟨h.2, h.1⟩

/-- `∀` respects provable equivalence of bodies. -/
lemma all_iff2 (i : V) {a b : V} (h : Iff2 a b) : Iff2 (wal i a) (wal i b) :=
  ⟨ValidatorQuantifierCore254.all_mono i h.1, ValidatorQuantifierCore254.all_mono i h.2⟩

/-- `a ↔ ¬b` gives `¬a ↔ b`. -/
lemma neg_swap {a b : V} (h : Iff2 a (vneg b)) : Iff2 (vneg a) b :=
  ⟨R2Ctx.ded1 (.mp (.ax (ValidatorQuantifierCore254.double_neg_elim b))
      (Kalmar.deduction cProv_classical (.mp h1 (.mp (.ax h.2) h0)))),
   R2Ctx.ded2 (.mp (.mp (.ax h.1) h0) h1)⟩

/-- `¬` respects provable equivalence. -/
lemma neg_iff2 {a b : V} (h : Iff2 a b) : Iff2 (vneg a) (vneg b) :=
  ⟨ValidatorQuantifierCore254.contrapose_of h.2, ValidatorQuantifierCore254.contrapose_of h.1⟩

/-! ## The induction -/

section Induction

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance encode_sigma2 : 𝚺-[2]-Function₄[V] encode :=
  (encode_defined.graph_delta.to_definable).of_deltaOne
private instance wim_sigma2 : 𝚺-[2]-Function₂[V] wim := wim_defined.to_definable₀
private instance semiformula_sigma2 : 𝚺-[2]-Relation[V] (IsSemiformula ℒₛₑₜ) :=
  IsSemiformula.definable.of_deltaOne
private instance neg_sigma2 : 𝚺-[2]-Function₁[V] (neg ℒₛₑₜ) :=
  (neg.defined.graph_delta.to_definable).of_deltaOne

private lemma negEq_pi2 : 𝚷-[2]-Predicate[V]
    (fun p => ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p) := by
  unfold NegEq vneg
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

theorem encode_neg {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) : NegEq F B s p := by
  have main : ∀ p : V, ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun p => ∀ n F B s : V, IsSemiformula ℒₛₑₜ n p → NegEq F B s p)
    · exact negEq_pi2
    · intro p ih n F B s htyped
      rcases IsSemiformula.case_iff.mp htyped with
        (⟨k, R, v, hr, hv, rfl⟩ | ⟨k, R, v, hr, hv, rfl⟩ | rfl | rfl |
          ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · rw [NegEq, neg_rel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
          encode_rel F B s hr hv.isUTerm]
        exact ⟨self_imp _, self_imp _⟩
      · rw [NegEq, neg_nrel hr hv.isUTerm, encode_nrel F B s hr hv.isUTerm,
          encode_rel F B s hr hv.isUTerm]
        exact ⟨ValidatorQuantifierCore254.double_neg_intro _,
          ValidatorQuantifierCore254.double_neg_elim _⟩
      · simp only [NegEq, neg_verum, encode_verum, encode_falsum]
        exact ⟨cProv_ex_falso _, R2Ctx.ded1 (.mp h0 (.ax cProv_truth))⟩
      · simp only [NegEq, neg_falsum, encode_verum, encode_falsum]
        exact ⟨cProv_mp (cProv_k _ _) (self_imp 1), cProv_mp (cProv_k _ _) cProv_truth⟩
      · have ihp := ih p (by simp) n F B s hp
        have ihq := ih q (by simp) n F B s hq
        rw [NegEq, neg_and hp.isUFormula hq.isUFormula,
          encode_or F B s hp.isUFormula.neg hq.isUFormula.neg,
          encode_and F B s hp.isUFormula hq.isUFormula]
        exact and_case (b := encode F B s (neg ℒₛₑₜ q)) ihp ihq
      · have ihp := ih p (by simp) n F B s hp
        have ihq := ih q (by simp) n F B s hq
        rw [NegEq, neg_or hp.isUFormula hq.isUFormula,
          encode_and F B s hp.isUFormula.neg hq.isUFormula.neg,
          encode_or F B s hp.isUFormula hq.isUFormula]
        exact or_case ihp ihq
      · have ihp := ih p (by simp) (n + 1) F (s ∷ B) (s + 2) hp
        rw [NegEq, neg_all hp.isUFormula, encode_exs F B s hp.isUFormula.neg,
          encode_all F B s hp.isUFormula]
        exact neg_iff2 (all_iff2 s (neg_swap ihp))
      · have ihp := ih p (by simp) (n + 1) F (s ∷ B) (s + 2) hp
        rw [NegEq, neg_ex hp.isUFormula, encode_all F B s hp.isUFormula.neg,
          encode_exs F B s hp.isUFormula]
        exact dneg_right (all_iff2 s ihp)
  exact main p n F B s hp

end Induction

end LeanProofs.ZFCinPA.R2Neg
