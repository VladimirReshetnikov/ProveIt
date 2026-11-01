import DiophantineConsistency.HADeduction

/-! # Basic arithmetic proofs in conventional HA

Every result constructs the existing intuitionistic `HA.Derives` relation or
its finite-axiom wrapper. Sealed arithmetic and induction axioms are opened by
explicit binder operations. No classical PA proof, model, or external natural
number identity supplies an object-language arithmetic theorem.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

namespace Derives

theorem eq_symm {G : List Formula} {s t : Term} (h : Derives G (.eq s t)) :
    Derives G (.eq t s) := by
  have ha : Derives G (Formula.subst (Formula.instTerm s)
      (.eq (.var 0) (Term.rename Nat.succ s))) := by
    simpa only [Formula.subst, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ] using Derives.eqRefl G s
  have hb := Derives.eqElim G s t (.eq (.var 0) (Term.rename Nat.succ s)) h ha
  simpa only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using hb

theorem eq_trans {G : List Formula} {s t u : Term}
    (h : Derives G (.eq s t)) (h' : Derives G (.eq t u)) : Derives G (.eq s u) := by
  have ha : Derives G (Formula.subst (Formula.instTerm t)
      (.eq (Term.rename Nat.succ s) (.var 0))) := by
    simpa only [Formula.subst, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ] using h
  have hb := Derives.eqElim G t u (.eq (Term.rename Nat.succ s) (.var 0)) h' ha
  simpa only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using hb

/-- The hole is target variable zero; ambient terms are shifted beneath it. -/
theorem eq_congr_term {G : List Formula} {s t : Term} (c : Term)
    (h : Derives G (.eq s t)) :
    Derives G (.eq (Term.subst (Formula.instTerm s) c)
      (Term.subst (Formula.instTerm t) c)) := by
  have ha : Derives G (Formula.subst (Formula.instTerm s)
      (.eq (Term.rename Nat.succ (Term.subst (Formula.instTerm s) c)) c)) := by
    simpa only [Formula.subst, Formula.term_subst_instTerm_rename_succ] using
      Derives.eqRefl G (Term.subst (Formula.instTerm s) c)
  have hb := Derives.eqElim G s t
    (.eq (Term.rename Nat.succ (Term.subst (Formula.instTerm s) c)) c) h ha
  simpa only [Formula.subst, Formula.term_subst_instTerm_rename_succ] using hb

end Derives

namespace Relative

theorem eq_refl {B : Formula → Prop} {G : List Formula} (t : Term) :
    Relative B G (.eq t t) := relative_of_derives (.eqRefl G t)

theorem eq_symm {B : Formula → Prop} {G : List Formula} {s t : Term}
    (h : Relative B G (.eq s t)) : Relative B G (.eq t s) := by
  obtain ⟨L,hL,h⟩ := h
  exact ⟨L,hL,h.eq_symm⟩

theorem eq_trans {B : Formula → Prop} {G : List Formula} {s t u : Term}
    (h : Relative B G (.eq s t)) (h' : Relative B G (.eq t u)) :
    Relative B G (.eq s u) := h.combine h' (fun _ => Derives.eq_trans)

theorem eq_congr_term {B : Formula → Prop} {G : List Formula} {s t : Term}
    (c : Term) (h : Relative B G (.eq s t)) :
    Relative B G (.eq (Term.subst (Formula.instTerm s) c)
      (Term.subst (Formula.instTerm t) c)) := by
  obtain ⟨L,hL,h⟩ := h
  exact ⟨L,hL,h.eq_congr_term c⟩

theorem eq_succ {B : Formula → Prop} {G : List Formula} {s t : Term}
    (h : Relative B G (.eq s t)) : Relative B G (.eq (.succ s) (.succ t)) := by
  simpa only [Term.subst, Formula.instTerm] using h.eq_congr_term (.succ (.var 0))

theorem eq_add_left {B : Formula → Prop} {G : List Formula} {s t : Term}
    (u : Term) (h : Relative B G (.eq s t)) : Relative B G (.eq (.add s u) (.add t u)) := by
  simpa only [Term.subst, Formula.instTerm, Formula.term_subst_instTerm_rename_succ]
    using h.eq_congr_term (.add (.var 0) (Term.rename Nat.succ u))

theorem eq_add_right {B : Formula → Prop} {G : List Formula} {s t : Term}
    (u : Term) (h : Relative B G (.eq s t)) : Relative B G (.eq (.add u s) (.add u t)) := by
  simpa only [Term.subst, Formula.instTerm, Formula.term_subst_instTerm_rename_succ]
    using h.eq_congr_term (.add (Term.rename Nat.succ u) (.var 0))

theorem eq_mul_left {B : Formula → Prop} {G : List Formula} {s t : Term}
    (u : Term) (h : Relative B G (.eq s t)) : Relative B G (.eq (.mul s u) (.mul t u)) := by
  simpa only [Term.subst, Formula.instTerm, Formula.term_subst_instTerm_rename_succ]
    using h.eq_congr_term (.mul (.var 0) (Term.rename Nat.succ u))

theorem eq_mul_right {B : Formula → Prop} {G : List Formula} {s t : Term}
    (u : Term) (h : Relative B G (.eq s t)) : Relative B G (.eq (.mul u s) (.mul u t)) := by
  simpa only [Term.subst, Formula.instTerm, Formula.term_subst_instTerm_rename_succ]
    using h.eq_congr_term (.mul (Term.rename Nat.succ u) (.var 0))

theorem all_elim {B : Formula → Prop} {G : List Formula} {a : Formula}
    (t : Term) (h : Relative B G (.all a)) :
    Relative B G (Formula.subst (Formula.instTerm t) a) := by
  obtain ⟨L,hL,h⟩ := h
  exact ⟨L,hL,.allE _ _ t h⟩

/-- The sentence condition prevents a theory axiom from capturing the new variable. -/
theorem all_intro {B : Formula → Prop} (hB : Formula.Sentences B)
    {G : List Formula} {a : Formula}
    (h : Relative B (G.map (Formula.rename Nat.succ)) a) : Relative B G (.all a) := by
  obtain ⟨L,hL,h⟩ := h
  have hm : L.map (Formula.rename Nat.succ) = L := by
    calc
      L.map (Formula.rename Nat.succ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact Formula.rename_eq_of_sentence (hB x (hL x hx)) Nat.succ
      _ = L := List.map_id L
  refine ⟨L,hL,.allI _ _ ?_⟩
  simpa only [List.map_append, hm] using h

theorem close {B : Formula → Prop} (hB : Formula.Sentences B) (n : Nat)
    {a : Formula} (h : Relative B [] a) : Relative B [] (Formula.closeN n a) := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
      apply ih
      exact all_intro hB (G := []) (by simpa only [List.map_nil] using h)

/-- Opening a genuine finite universal closure, including all free parameters. -/
theorem open_rename {B : Formula → Prop} {G : List Formula} (k : Nat)
    (a : Formula) (r : Nat → Nat) (hf : ∀ n, Formula.Free n a → n < k)
    (h : Relative B G (Formula.closeN k a)) : Relative B G (Formula.rename r a) := by
  induction k generalizing a r with
  | zero =>
      have hs : Formula.Sentence a := fun n hn => Nat.not_lt_zero n (hf n hn)
      simpa only [Formula.closeN, Formula.rename_eq_of_sentence hs r] using h
  | succ k ih =>
      let tail : Nat → Nat := fun n => r (n+1)
      have hb : Relative B G (Formula.rename tail (.all a)) := by
        apply ih (.all a) tail
        · intro n hn
          have := hf (n+1) hn
          omega
        · exact h
      have hi := all_elim (.var (r 0)) hb
      have he : Formula.subst (Formula.instTerm (.var (r 0)))
          (Formula.rename (SetTheory.up tail) a) = Formula.rename r a := by
        rw [Formula.subst_instTerm_var, Formula.rename_comp]
        apply Formula.rename_ext
        intro n
        cases n <;> rfl
      exact he ▸ hi

end Relative

namespace Arithmetic

theorem axiom_body {a : Formula} (h : Formula.Ax_s (Formula.sealPA a)) : Proves a := by
  have hb := Relative.open_rename (Formula.bound a) a (fun n => n)
    (fun n hn => Formula.free_lt_bound a n hn) (proves_axiom h)
  simpa only [Proves, List.map_nil, Formula.rename_id] using hb

theorem reclose {a : Formula} (n : Nat) (h : Proves a) : Proves (Formula.closeN n a) :=
  Relative.close Formula.Ax_s_sentences n h

theorem succ_inj (s t : Term) : Proves (.imp (.eq (.succ s) (.succ t)) (.eq s t)) := by
  have h := Relative.all_elim t (Relative.all_elim s (axiom_body Formula.Ax_s_succInj))
  simpa only [Proves, List.map_nil, Formula.succInj, Formula.subst, Formula.instTerm, Term.subst,
    Term.upSubst, Formula.term_subst_instTerm_rename_succ] using h

theorem succ_ne_zero (t : Term) : Proves (.imp (.eq (.succ t) .zero) .bot) := by
  have h := Relative.all_elim t (axiom_body Formula.Ax_s_zeroNotSucc)
  simpa only [Proves, List.map_nil, Formula.zeroNotSucc, Formula.subst, Formula.instTerm, Term.subst] using h

theorem add_zero (t : Term) : Proves (.eq (.add t .zero) t) := by
  have h := Relative.all_elim t (axiom_body Formula.Ax_s_addZero)
  simpa only [Proves, List.map_nil, Formula.addZero, Formula.subst, Formula.instTerm, Term.subst] using h

theorem add_succ (s t : Term) : Proves (.eq (.add s (.succ t)) (.succ (.add s t))) := by
  have h := Relative.all_elim t (Relative.all_elim s (axiom_body Formula.Ax_s_addSucc))
  simpa only [Proves, List.map_nil, Formula.addSucc, Formula.subst, Formula.instTerm, Term.subst,
    Term.upSubst, Formula.term_subst_instTerm_rename_succ] using h

theorem mul_zero (t : Term) : Proves (.eq (.mul t .zero) .zero) := by
  have h := Relative.all_elim t (axiom_body Formula.Ax_s_mulZero)
  simpa only [Proves, List.map_nil, Formula.mulZero, Formula.subst, Formula.instTerm, Term.subst] using h

theorem mul_succ (s t : Term) : Proves (.eq (.mul s (.succ t)) (.add (.mul s t) s)) := by
  have h := Relative.all_elim t (Relative.all_elim s (axiom_body Formula.Ax_s_mulSucc))
  simpa only [Proves, List.map_nil, Formula.mulSucc, Formula.subst, Formula.instTerm, Term.subst,
    Term.upSubst, Formula.term_subst_instTerm_rename_succ] using h

/-- This is the actual first-order induction schema, with finite axiom lists. -/
theorem induction {G : List Formula} (a : Formula)
    (hzero : Relative Formula.Ax_s G (Formula.subst Formula.substZero a))
    (hsucc : Relative Formula.Ax_s G (.all (.imp a (Formula.subst Formula.substSuccVar a)))) :
    Relative Formula.Ax_s G (.all a) := by
  have hi : Relative Formula.Ax_s G (Formula.inductionForm a) :=
    (axiom_body (Formula.Ax_s_induction a)).weaken (by simp)
  exact hi.mp (hzero.and_intro hsucc)

/-- An induction theorem, not one of the six arithmetic axiom instances. -/
theorem zero_add_all : Proves (.all (.eq (.add .zero (.var 0)) (.var 0))) := by
  let a : Formula := .eq (.add .zero (.var 0)) (.var 0)
  apply induction a
  · simpa only [Proves, List.map_nil, a, Formula.subst, Term.subst, Formula.substZero] using add_zero .zero
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    have ih : Relative Formula.Ax_s [a] a :=
      relative_of_derives (.ass _ _ List.mem_cons_self)
    have hs : Relative Formula.Ax_s [a]
        (.eq (.add .zero (.succ (.var 0))) (.succ (.add .zero (.var 0)))) :=
      (add_succ .zero (.var 0)).weaken (by simp)
    have hh := hs.eq_trans ih.eq_succ
    simpa only [Proves, List.map_nil, a, Formula.subst, Term.subst, Formula.substSuccVar] using hh

theorem zero_add (t : Term) : Proves (.eq (.add .zero t) t) := by
  have h := Relative.all_elim t zero_add_all
  simpa only [Proves, List.map_nil, Formula.subst, Term.subst, Formula.instTerm] using h

/-- This is a proved HA equality; translating Foundation's `x+1` into `S x`
requires this theorem rather than a definitional syntax identification. -/
theorem add_one (t : Term) : Proves (.eq (.add t (.succ .zero)) (.succ t)) :=
  (add_succ t .zero).eq_trans (add_zero t).eq_succ

end Arithmetic
end DiophantineConsistency.HA
