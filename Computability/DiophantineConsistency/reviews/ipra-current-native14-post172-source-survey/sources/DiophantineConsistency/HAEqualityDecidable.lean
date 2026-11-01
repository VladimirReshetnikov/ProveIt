import DiophantineConsistency.HANaturalCases

/-! Equality decidability inside conventional HA, constructed by formula
induction and the proved zero/successor split. The eliminators retain every
finite theory axiom and shift all open assumptions at an existential binder.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

namespace Relative

theorem hypothesis {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : a ∈ G) : Relative B G a := relative_of_derives (.ass G a h)

theorem or_elim {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (h : Relative B G (.or a b)) (ha : Relative B (a :: G) c)
    (hb : Relative B (b :: G) c) : Relative B G c := by
  have hr : Relative B G (.imp (.or a b) c) :=
    ha.imp_intro.combine hb.imp_intro fun H hp hq =>
      .impI H (.or a b) c (.orE _ a b c (.ass _ _ List.mem_cons_self)
        (((hp.prepend (.or a b)).prepend a).mp (.ass _ _ List.mem_cons_self))
        (((hq.prepend (.or a b)).prepend b).mp (.ass _ _ List.mem_cons_self)))
  exact hr.mp h

/-- The eigenvariable shifts the entire open context and the conclusion.
Only sentence axioms may remain unchanged across that shift. -/
theorem ex_elim {B : Formula → Prop} (hB : Formula.Sentences B)
    {G : List Formula} {a c : Formula} (h : Relative B G (.ex a))
    (hc : Relative B (a :: G.map (Formula.rename Nat.succ))
      (Formula.rename Nat.succ c)) : Relative B G c := by
  obtain ⟨L, hL, hp⟩ := h
  obtain ⟨K, hK, hq⟩ := hc
  have hLK : ∀ x ∈ L ++ K, B x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hL x) (hK x)
  have hm : (L ++ K).map (Formula.rename Nat.succ) = L ++ K := by
    calc
      (L ++ K).map (Formula.rename Nat.succ) = (L ++ K).map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact Formula.rename_eq_of_sentence (hB x (hLK x hx)) Nat.succ
      _ = L ++ K := List.map_id _
  refine ⟨L ++ K, hLK, .exE _ a c (hp.weaken _ ?_) ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (Or.inl h)) Or.inr
  · rw [List.map_append, hm]
    apply hq.weaken
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    exact hx.elim (fun h => Or.inr (Or.inl (Or.inr h)))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))

theorem eq_elim {B : Formula → Prop} {G : List Formula} {s t : Term}
    (a : Formula) (he : Relative B G (.eq s t))
    (h : Relative B G (Formula.subst (Formula.instTerm s) a)) :
    Relative B G (Formula.subst (Formula.instTerm t) a) :=
  he.combine h (fun H => Derives.eqElim H s t a)

end Relative

namespace EqualityDecidable

/-- Negation is implication to bottom, not a new classical connective. -/
def cases (s t : Term) : Formula := .or (.eq s t) (.imp (.eq s t) .bot)

theorem rename_cases (r : Nat → Nat) (s t : Term) :
    Formula.rename r (cases s t) = cases (Term.rename r s) (Term.rename r t) := rfl

theorem subst_cases (r : Nat → Term) (s t : Term) :
    Formula.subst r (cases s t) = cases (Term.subst r s) (Term.subst r t) := rfl

theorem refl {B : Formula → Prop} {G : List Formula} (s : Term) :
    Relative B G (cases s s) := Relative.or_intro_left _ (Relative.eq_refl s)

/-- Transport on the right preserves the arbitrary left term's free variables. -/
theorem transport_right {B : Formula → Prop} {G : List Formula} {s t u : Term}
    (h : Relative B G (cases s t)) (he : Relative B G (.eq t u)) :
    Relative B G (cases s u) := by
  have h' : Relative B G (Formula.subst (Formula.instTerm t)
      (cases (Term.rename Nat.succ s) (.var 0))) := by
    simpa only [subst_cases, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ] using h
  have hh := Relative.eq_elim (cases (Term.rename Nat.succ s) (.var 0)) he h'
  simpa only [subst_cases, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using hh

theorem zero_succ {G : List Formula} (t : Term) :
    Relative Formula.Ax_s G (cases .zero (.succ t)) := by
  apply Relative.or_intro_right
  apply Relative.imp_intro
  have he : Relative Formula.Ax_s (.eq .zero (.succ t) :: G) (.eq .zero (.succ t)) :=
    Relative.hypothesis List.mem_cons_self
  exact ((Arithmetic.succ_ne_zero t).weaken (by simp)).mp he.eq_symm

theorem succ_zero {G : List Formula} (s : Term) :
    Relative Formula.Ax_s G (cases (.succ s) .zero) :=
  Relative.or_intro_right _ ((Arithmetic.succ_ne_zero s).weaken (by simp))

theorem succ_cases {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (cases s t)) :
    Relative Formula.Ax_s G (cases (.succ s) (.succ t)) := by
  apply Relative.or_elim h
  · exact Relative.or_intro_left _
      (Relative.eq_succ (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    have hn : Relative Formula.Ax_s
        (.eq (.succ s) (.succ t) :: .imp (.eq s t) .bot :: G) (.imp (.eq s t) .bot) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    have he : Relative Formula.Ax_s
        (.eq (.succ s) (.succ t) :: .imp (.eq s t) .bot :: G) (.eq (.succ s) (.succ t)) :=
      Relative.hypothesis List.mem_cons_self
    exact hn.mp (((Arithmetic.succ_inj s t).weaken (by simp)).mp he)

/-- The arbitrary target is eliminated by the HA predecessor theorem. -/
theorem zero_cases (t : Term) : Proves (cases .zero t) := by
  apply Relative.or_elim (NaturalCases.zero_or_succ t)
  · exact transport_right (refl .zero)
      (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))
  · apply Relative.ex_elim Formula.Ax_s_sentences
      (Relative.hypothesis List.mem_cons_self)
    change Relative Formula.Ax_s _ (cases .zero (Term.rename Nat.succ t))
    exact transport_right (zero_succ (.var 0))
      (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))

/-- The induction variable is x; y is bound by the inner universal quantifier. -/
def body : Formula := .all (cases (.var 1) (.var 0))

theorem body_zero : Formula.subst Formula.substZero body =
    .all (cases .zero (.var 0)) := rfl

theorem body_succ : Formula.subst Formula.substSuccVar body =
    .all (cases (.succ (.var 1)) (.var 0)) := rfl

/-- A single actual formula induction on x, with a universally quantified y.
The successor branch eliminates y's existential predecessor with both ambient
variables and the induction hypothesis shifted through that binder. -/
theorem eq_decidable_all : Proves (.all body) := by
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
    · exact transport_right (succ_zero (.var 1))
        (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))
    · apply Relative.ex_elim Formula.Ax_s_sentences
        (Relative.hypothesis List.mem_cons_self)
      change Relative Formula.Ax_s _ (cases (.succ (.var 2)) (.var 1))
      have hi : Relative Formula.Ax_s
          (.eq (.var 1) (.succ (.var 0)) ::
            (.ex (.eq (.var 1) (.succ (.var 0))) ::
              [body].map (Formula.rename Nat.succ)).map (Formula.rename Nat.succ))
          (.all (cases (.var 3) (.var 0))) := by
        apply Relative.hypothesis
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          body, Formula.rename, cases, Term.rename, SetTheory.up]
        exact Or.inr (Or.inr (Or.inl True.intro))
      have hd := Relative.all_elim (.var 0) hi
      change Relative Formula.Ax_s _ (cases (.var 2) (.var 0)) at hd
      exact transport_right (succ_cases hd)
        (Relative.eq_symm (Relative.hypothesis List.mem_cons_self))

/-- The two eliminations instantiate free parameters without capture. -/
theorem eq_decidable (s t : Term) : Proves (cases s t) := by
  have h := Relative.all_elim t (Relative.all_elim s eq_decidable_all)
  simpa only [Proves, body, cases, Formula.subst, Formula.instTerm, Term.subst,
    Term.upSubst, Formula.term_subst_instTerm_rename_succ] using h

end EqualityDecidable
end DiophantineConsistency.HA
