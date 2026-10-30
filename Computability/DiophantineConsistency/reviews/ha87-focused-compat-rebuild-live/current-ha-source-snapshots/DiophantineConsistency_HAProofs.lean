import PAHF.PACore

/-! # Heyting arithmetic proof existence over the existing arithmetic syntax

`HA.Derives` is intuitionistic first-order natural deduction with equality.
It has no excluded-middle, double-negation-elimination, semantic-reflection,
or choice rule. Its terms and binder operations are exactly the existing
`SetTheory.PA` arithmetic syntax. `HA.Proves` admits a finite list of the six
arithmetic axioms and universally closed first-order induction instances.

The embedding into classical PA is one-way. In particular, this file does
not turn an external arithmetic theorem or a classical derivation into an
HA proof. A proof-existence statement suffices; no serialized proof is needed.
-/

set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

/-- Intuitionistic natural deduction. Quantifier rules explicitly shift the
context, so the newly introduced variable cannot occur freely in an old
assumption. Equality elimination is the ordinary Leibniz rule. -/
inductive Derives : List Formula → Formula → Prop
  | ass : ∀ G a, a ∈ G → Derives G a
  | impI : ∀ G a b, Derives (a :: G) b → Derives G (.imp a b)
  | impE : ∀ G a b, Derives G (.imp a b) → Derives G a → Derives G b
  | botE : ∀ G a, Derives G .bot → Derives G a
  | andI : ∀ G a b, Derives G a → Derives G b → Derives G (.and a b)
  | andE1 : ∀ G a b, Derives G (.and a b) → Derives G a
  | andE2 : ∀ G a b, Derives G (.and a b) → Derives G b
  | orI1 : ∀ G a b, Derives G a → Derives G (.or a b)
  | orI2 : ∀ G a b, Derives G b → Derives G (.or a b)
  | orE : ∀ G a b c, Derives G (.or a b) → Derives (a :: G) c →
      Derives (b :: G) c → Derives G c
  | allI : ∀ G a, Derives (G.map (Formula.rename Nat.succ)) a →
      Derives G (.all a)
  | allE : ∀ G a t, Derives G (.all a) →
      Derives G (Formula.subst (Formula.instTerm t) a)
  | exI : ∀ G a t, Derives G (Formula.subst (Formula.instTerm t) a) →
      Derives G (.ex a)
  | exE : ∀ G a c, Derives G (.ex a) →
      Derives (a :: G.map (Formula.rename Nat.succ)) (Formula.rename Nat.succ c) →
      Derives G c
  | eqRefl : ∀ G t, Derives G (.eq t t)
  | eqElim : ∀ G s t a, Derives G (.eq s t) →
      Derives G (Formula.subst (Formula.instTerm s) a) →
      Derives G (Formula.subst (Formula.instTerm t) a)

namespace Derives

/-- Forget only the restriction on logical rules. There is no reverse map. -/
theorem erase {G : List Formula} {a : Formula} (h : Derives G a) :
    Formula.Prov G a := by
  induction h with
  | ass G a h => exact .P_ass G a h
  | impI G a b _ ih => exact .P_impI G a b ih
  | impE G a b _ _ ih₁ ih₂ => exact .P_impE G a b ih₁ ih₂
  | botE G a _ ih => exact .P_botE G a ih
  | andI G a b _ _ ih₁ ih₂ => exact .P_andI G a b ih₁ ih₂
  | andE1 G a b _ ih => exact .P_andE1 G a b ih
  | andE2 G a b _ ih => exact .P_andE2 G a b ih
  | orI1 G a b _ ih => exact .P_orI1 G a b ih
  | orI2 G a b _ ih => exact .P_orI2 G a b ih
  | orE G a b c _ _ _ ih₁ ih₂ ih₃ => exact .P_orE G a b c ih₁ ih₂ ih₃
  | allI G a _ ih => exact .P_allI G a ih
  | allE G a t _ ih => exact .P_allE G a t ih
  | exI G a t _ ih => exact .P_exI G a t ih
  | exE G a c _ _ ih₁ ih₂ => exact .P_exE G a c ih₁ ih₂
  | eqRefl G t => exact .P_eqRefl G t
  | eqElim G s t a _ _ ih₁ ih₂ => exact .P_eqElim G s t a ih₁ ih₂

theorem weaken {G : List Formula} {a : Formula} (h : Derives G a) :
    ∀ G', (∀ x ∈ G, x ∈ G') → Derives G' a := by
  induction h with
  | ass G a h => intro G' hs; exact .ass G' a (hs a h)
  | impI G a b _ ih =>
      intro G' hs; exact .impI G' a b (ih _ (Formula.cons_sub hs))
  | impE G a b _ _ ih₁ ih₂ =>
      intro G' hs; exact .impE G' a b (ih₁ G' hs) (ih₂ G' hs)
  | botE G a _ ih => intro G' hs; exact .botE G' a (ih G' hs)
  | andI G a b _ _ ih₁ ih₂ =>
      intro G' hs; exact .andI G' a b (ih₁ G' hs) (ih₂ G' hs)
  | andE1 G a b _ ih => intro G' hs; exact .andE1 G' a b (ih G' hs)
  | andE2 G a b _ ih => intro G' hs; exact .andE2 G' a b (ih G' hs)
  | orI1 G a b _ ih => intro G' hs; exact .orI1 G' a b (ih G' hs)
  | orI2 G a b _ ih => intro G' hs; exact .orI2 G' a b (ih G' hs)
  | orE G a b c _ _ _ ih₁ ih₂ ih₃ =>
      intro G' hs
      exact .orE G' a b c (ih₁ G' hs)
        (ih₂ _ (Formula.cons_sub hs)) (ih₃ _ (Formula.cons_sub hs))
  | allI G a _ ih =>
      intro G' hs; exact .allI G' a (ih _ (Formula.mem_map_sub hs))
  | allE G a t _ ih => intro G' hs; exact .allE G' a t (ih G' hs)
  | exI G a t _ ih => intro G' hs; exact .exI G' a t (ih G' hs)
  | exE G a c _ _ ih₁ ih₂ =>
      intro G' hs
      exact .exE G' a c (ih₁ G' hs)
        (ih₂ _ (Formula.cons_sub (Formula.mem_map_sub hs)))
  | eqRefl G t => intro G' _; exact .eqRefl G' t
  | eqElim G s t a _ _ ih₁ ih₂ =>
      intro G' hs; exact .eqElim G' s t a (ih₁ G' hs) (ih₂ G' hs)

theorem identity (G : List Formula) (a : Formula) : Derives G (.imp a a) :=
  .impI G a a (.ass (a :: G) a (List.mem_cons_self))

end Derives

/-- Finite use of a supplied object-language axiom set. -/
def Relative (B : Formula → Prop) (G : List Formula) (a : Formula) : Prop :=
  ∃ L, (∀ x ∈ L, B x) ∧ Derives (L ++ G) a

/-- Conventional first-order HA: the usual PA axiom schema, with the
intuitionistic equality calculus above instead of classical deduction. -/
def Proves (a : Formula) : Prop := Relative Formula.Ax_s [] a

theorem relative_of_derives {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Derives G a) : Relative B G a :=
  ⟨[], fun _ hx => False.elim (List.not_mem_nil hx), h⟩

theorem relative_axiom {B : Formula → Prop} {G : List Formula} {a : Formula}
    (ha : B a) : Relative B G a := by
  refine ⟨[a], ?_, .ass _ a ?_⟩
  · intro x hx
    simpa only [List.mem_singleton.mp hx] using ha
  · exact List.mem_cons_self

theorem proves_axiom {a : Formula} (ha : Formula.Ax_s a) : Proves a :=
  relative_axiom ha

/-- Every first-order induction instance, with every parameter universally
closed, is an HA axiom. This is not induction on all metatheoretic predicates. -/
theorem induction_axiom (a : Formula) :
    Proves (Formula.sealPA (Formula.inductionForm a)) :=
  proves_axiom (Formula.Ax_s_induction a)

theorem relative_to_classical {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) : Formula.BProv B G a := by
  obtain ⟨L,hL,h⟩ := h
  exact ⟨L,hL,h.erase⟩

theorem to_classical {a : Formula} (h : Proves a) :
    Formula.BProv Formula.Ax_s [] a := relative_to_classical h

theorem proves_identity (a : Formula) : Proves (.imp a a) :=
  relative_of_derives (Derives.identity [] a)

end DiophantineConsistency.HA
