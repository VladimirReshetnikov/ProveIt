import DiophantineConsistency.FoundationHAOrderWitnesses

/-! # Actual trichotomy by HA formula induction

The proof follows zero/successor decomposition inside HA, preserving strict
order with its actual predecessor witness. A finite disjunction constructor
then supplies the literal nested GG encoding; no classical totality oracle,
order DNE or negative-translation recursion is used.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderTrichotomy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAOrderBase
open SetTheory.PA HA

def tri (s t : Term) : Formula :=
  .or (ltFormula s t) (.or (.eq s t) (ltFormula t s))

theorem subst_tri (σ : Nat → Term) (s t : Term) :
    Formula.subst σ (tri s t) = tri (Term.subst σ s) (Term.subst σ t) := by
  simp only [tri, Formula.subst, subst_ltFormula]

theorem rename_tri (r : Nat → Nat) (s t : Term) :
    Formula.rename r (tri s t) = tri (Term.rename r s) (Term.rename r t) := by
  simp only [tri, Formula.rename, rename_ltFormula]

/-- Leibniz transport through the complete three-way formula, with a fresh
hole and shifted ambient terms. -/
theorem transport_right {G : List Formula} {s t u : Term}
    (h : Relative Formula.Ax_s G (tri s t)) (he : Relative Formula.Ax_s G (.eq t u)) :
    Relative Formula.Ax_s G (tri s u) := by
  have h₀ : Relative Formula.Ax_s G (Formula.subst (Formula.instTerm t)
      (tri (Term.rename Nat.succ s) (.var 0))) := by
    simpa only [subst_tri, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ] using h
  have h₁ := Relative.eq_elim (tri (Term.rename Nat.succ s) (.var 0)) he h₀
  simpa only [subst_tri, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h₁

theorem zero_cases (t : Term) : Proves (tri .zero t) := by
  apply Relative.or_elim (FoundationHAOrderBase.zero_le t)
  · exact Relative.or_intro_right _ (Relative.or_intro_left _
      (Relative.hypothesis List.mem_cons_self))
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)

theorem succ_zero (s : Term) : Proves (tri (.succ s) .zero) := by
  apply Relative.or_intro_right
  apply Relative.or_intro_right
  apply Relative.ex_intro _ s
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ, Term.rename] using Arithmetic.zero_add (.succ s)

/-- Successor preserves strict order with exactly the original predecessor. -/
theorem lt_succ {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (ltFormula s t)) :
    Relative Formula.Ax_s G (ltFormula (.succ s) (.succ t)) := by
  apply Relative.ex_elim Formula.Ax_s_sentences h
  rw [rename_ltFormula]
  apply Relative.ex_intro _ (.var 0)
  simp only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ]
  have he : Relative Formula.Ax_s
      (.eq (.add (Term.rename Nat.succ s) (.succ (.var 0))) (Term.rename Nat.succ t) ::
        G.map (Formula.rename Nat.succ))
      (.eq (.add (Term.rename Nat.succ s) (.succ (.var 0))) (Term.rename Nat.succ t)) :=
    Relative.hypothesis List.mem_cons_self
  exact ((Arithmetic.succ_add (Term.rename Nat.succ s) (.succ (.var 0))).weaken
    (by simp)).eq_trans he.eq_succ

theorem succ_cases {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (tri s t)) :
    Relative Formula.Ax_s G (tri (.succ s) (.succ t)) := by
  apply Relative.or_elim h
  · exact Relative.or_intro_left _ (lt_succ (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_elim (Relative.hypothesis List.mem_cons_self)
    · exact Relative.or_intro_right _ (Relative.or_intro_left _
        (Relative.hypothesis List.mem_cons_self).eq_succ)
    · exact Relative.or_intro_right _ (Relative.or_intro_right _
        (lt_succ (Relative.hypothesis List.mem_cons_self)))

/-- x is the induction variable; y is bound by the inner universal. -/
def body : Formula := .all (tri (.var 1) (.var 0))

theorem body_zero : Formula.subst Formula.substZero body =
    .all (tri .zero (.var 0)) := rfl

theorem body_succ : Formula.subst Formula.substSuccVar body =
    .all (tri (.succ (.var 1)) (.var 0)) := rfl

/-- One actual HA formula-induction proof, not induction in a standard model.
The successor case shifts both the IH and arbitrary y through its predecessor binder. -/
theorem tri_all : Proves (.all body) := by
  apply Arithmetic.induction body
  · rw [body_zero]
    apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    exact zero_cases (.var 0)
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    rw [body_succ]
    apply Relative.all_intro Formula.Ax_s_sentences
    have hy : Relative Formula.Ax_s ([body].map (Formula.rename Nat.succ))
        (.or (.eq (.var 0) .zero) (.ex (.eq (.var 1) (.succ (.var 0))))) :=
      (NaturalCases.zero_or_succ (.var 0)).weaken (by simp)
    apply Relative.or_elim hy
    · exact transport_right ((succ_zero (.var 1)).weaken (by simp))
        (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))
    · apply Relative.ex_elim Formula.Ax_s_sentences
        (Relative.hypothesis List.mem_cons_self)
      change Relative Formula.Ax_s _ (tri (.succ (.var 2)) (.var 1))
      have hi : Relative Formula.Ax_s
          (.eq (.var 1) (.succ (.var 0)) ::
            (.ex (.eq (.var 1) (.succ (.var 0))) ::
              [body].map (Formula.rename Nat.succ)).map (Formula.rename Nat.succ))
          (.all (tri (.var 3) (.var 0))) := by
        apply Relative.hypothesis
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          body, Formula.rename, tri, ltFormula, Term.rename, SetTheory.up]
        exact Or.inr (Or.inr (Or.inl True.intro))
      have hd := Relative.all_elim (.var 0) hi
      change Relative Formula.Ax_s _ (tri (.var 2) (.var 0)) at hd
      exact transport_right (succ_cases hd)
        (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))

theorem trichotomy (s t : Term) : Proves (tri s t) := by
  have h := Relative.all_elim t (Relative.all_elim s tri_all)
  simpa only [Proves, body, tri, Formula.subst, subst_ltFormula,
    Formula.instTerm, Term.subst, Term.upSubst,
    Formula.term_subst_instTerm_rename_succ] using h

/-- The actual right-associated source disjunction's three negative leaves. -/
def encodedThree (a b c : Formula) : Formula :=
  neg (.and (neg (doubleNeg a))
    (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c))))))

private theorem dni {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) : Relative B G (doubleNeg a) :=
  (relative_of_derives (Derives.doubleNeg_intro G a)).mp h

/-- A finite three-branch proof, not a recursive translation. The inner
negative encoding is retained as-is, without an extra double negation. -/
theorem encoded_three {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (h : Relative B G (.or a (.or b c))) : Relative B G (encodedThree a b c) := by
  apply Relative.imp_intro
  apply Relative.or_elim (h.prepend (.and (neg (doubleNeg a))
    (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c)))))))
  · have hn : Relative B
        (a :: .and (neg (doubleNeg a))
          (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c))))) :: G)
        (.and (neg (doubleNeg a))
          (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c)))))) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact hn.and_left.mp (dni (Relative.hypothesis List.mem_cons_self))
  · have hn : Relative B
        (.or b c :: .and (neg (doubleNeg a))
          (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c))))) :: G)
        (.and (neg (doubleNeg a))
          (neg (neg (.and (neg (doubleNeg b)) (neg (doubleNeg c)))))) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact hn.and_right.mp (encoded_or (Relative.hypothesis List.mem_cons_self))

/-- Literal full source axiom, including its nested disjunction association. -/
theorem ltTri : Proves (sentence PeanoMinus.Axiom.ltTriᴺ) := by
  change Proves (Formula.closeN 2
    (encodedThree (ltFormula (.var 1) (.var 0)) (.eq (.var 1) (.var 0))
      (ltFormula (.var 0) (.var 1))))
  exact Arithmetic.reclose 2 (encoded_three (trichotomy (.var 1) (.var 0)))

end DiophantineConsistency.FoundationHAOrderTrichotomy
