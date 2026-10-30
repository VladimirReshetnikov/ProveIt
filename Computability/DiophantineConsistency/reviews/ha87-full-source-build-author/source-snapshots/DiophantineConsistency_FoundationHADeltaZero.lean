import DiophantineConsistency.HABoundedQuantifiers
import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-! Ordinary interpretation of actual Foundation bounded formulas in HA.

This uses the existing eight-constructor NNF syntax and its actual DeltaZero
predicate. Positive bounds mean absence of bound slot zero, not numerical
positivity. The universal guard is an NNF disjunction; its replacement by an
implication is proved in HA using the decision of the order atom. There is
no GG comparison, checker normalization, or semantic decision oracle here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHADeltaZero
open LO LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax HABoundedQuantifiers
open scoped LO.FirstOrder

/-- Ordinary NNF interpretation, with explicit capture-avoiding environments. -/
def ordinaryAux {ξ : Type*} {n : Nat} (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    Semiformula ℒₒᵣ ξ n → SetTheory.PA.Formula
  | .verum => .imp .bot .bot
  | .falsum => .bot
  | .rel .eq v => .eq (termAux bv fv (v 0)) (termAux bv fv (v 1))
  | .rel .lt v => ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1))
  | .nrel .eq v => neg (.eq (termAux bv fv (v 0)) (termAux bv fv (v 1)))
  | .nrel .lt v => neg (ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1)))
  | .and p q => .and (ordinaryAux bv fv p) (ordinaryAux bv fv q)
  | .or p q => .or (ordinaryAux bv fv p) (ordinaryAux bv fv q)
  | .all p => .all (ordinaryAux (liftBound bv) (liftFree fv) p)
  | .exs p => .ex (ordinaryAux (liftBound bv) (liftFree fv) p)

/-- Exact extraction of an outer bound, retaining every ambient parameter. -/
theorem positive_bound {ξ : Type*} {n : Nat} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    {t : Semiterm ℒₒᵣ ξ (n+1)} (ht : t.Positive) :
    ∃ u : Semiterm ℒₒᵣ ξ n, t = Rew.bShift u ∧
      termAux (liftBound bv) (liftFree fv) t = SetTheory.PA.Term.rename Nat.succ (termAux bv fv u) := by
  obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht
  exact ⟨u, rfl, termAux_bShift bv fv u⟩

/-- NNF bounded universality has a disjunctive, rather than primitive, guard. -/
theorem ordinary_ball {ξ : Type*} {n : Nat} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (u : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n+1)) :
    ordinaryAux bv fv (∀⁰[“x. x < !!(Rew.bShift u)”] p) =
      .all (.or (neg (ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ (termAux bv fv u))))
        (ordinaryAux (liftBound bv) (liftFree fv) p)) := by
  change SetTheory.PA.Formula.all (.or (neg (ltFormula (.var 0)
    (termAux (liftBound bv) (liftFree fv) (Rew.bShift u)))) _) = _
  rw [termAux_bShift]

theorem ordinary_bex {ξ : Type*} {n : Nat} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (u : Semiterm ℒₒᵣ ξ n) (p : Semiformula ℒₒᵣ ξ (n+1)) :
    ordinaryAux bv fv (∃⁰[“x. x < !!(Rew.bShift u)”] p) =
      bex (termAux bv fv u) (ordinaryAux (liftBound bv) (liftFree fv) p) := by
  change SetTheory.PA.Formula.ex (.and (ltFormula (.var 0)
    (termAux (liftBound bv) (liftFree fv) (Rew.bShift u))) _) = _
  rw [termAux_bShift]
  rfl

private theorem explode {G : List SetTheory.PA.Formula} {a : SetTheory.PA.Formula}
    (h : Relative SetTheory.PA.Formula.Ax_s G .bot) : Relative SetTheory.PA.Formula.Ax_s G a := by
  obtain ⟨L,hL,hp⟩ := h
  exact ⟨L,hL,.botE _ _ hp⟩

private theorem dec_neg {G : List SetTheory.PA.Formula} {a : SetTheory.PA.Formula}
    (ha : Relative SetTheory.PA.Formula.Ax_s G (dec a)) :
    Relative SetTheory.PA.Formula.Ax_s G (dec (neg a)) := by
  apply Relative.or_elim ha
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    exact (Relative.hypothesis List.mem_cons_self).mp
      (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)

private theorem dec_map {a b : SetTheory.PA.Formula} (hd : Proves (dec a))
    (hf : Proves (.imp a b)) (hb : Proves (.imp b a)) : Proves (dec b) := by
  apply Relative.or_elim hd
  · exact Relative.or_intro_left _ ((hf.prepend _).mp (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    exact (Relative.hypothesis (G := [b, neg a])
      (List.mem_cons_of_mem _ List.mem_cons_self)).mp
      (((hb.prepend _).prepend _).mp (Relative.hypothesis List.mem_cons_self))

/-- Forward guard conversion requires no decision premise. -/
theorem guard_forward (l a : SetTheory.PA.Formula) :
    Proves (.imp (.or (neg l) a) (.imp l a)) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  apply Relative.or_elim (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact explode ((Relative.hypothesis List.mem_cons_self).mp
      (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact Relative.hypothesis List.mem_cons_self

/-- The reverse conversion uses an actual HA proof deciding its guard. -/
theorem guard_reverse {l : SetTheory.PA.Formula} (a : SetTheory.PA.Formula)
    (hd : Proves (dec l)) : Proves (.imp (.imp l a) (.or (neg l) a)) := by
  apply Relative.imp_intro
  apply Relative.or_elim (hd.prepend _)
  · exact Relative.or_intro_right _ ((Relative.hypothesis
      (List.mem_cons_of_mem _ List.mem_cons_self)).mp (Relative.hypothesis List.mem_cons_self))
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)

/-- Reclosing shifts the entire antecedent context under the eigenvariable. -/
theorem all_imp {a b : SetTheory.PA.Formula} (h : Proves (.imp a b)) :
    Proves (.imp (.all a) (.all b)) := by
  apply Relative.imp_intro
  apply Relative.all_intro SetTheory.PA.Formula.Ax_s_sentences
  have hs : Relative SetTheory.PA.Formula.Ax_s
      ([.all a].map (SetTheory.PA.Formula.rename Nat.succ))
      (SetTheory.PA.Formula.rename Nat.succ (.all a)) :=
    Relative.hypothesis List.mem_cons_self
  have ha := Relative.all_elim (.var 0) hs
  have hb : Relative SetTheory.PA.Formula.Ax_s
      ([.all a].map (SetTheory.PA.Formula.rename Nat.succ)) a := by
    simpa only [SetTheory.PA.Formula.rename,
      SetTheory.PA.Formula.subst_instTerm_var_zero_rename_up_succ] using ha
  exact (h.weaken (by simp)).mp hb

theorem guarded_all_decidable (t : PTerm) (a : SetTheory.PA.Formula)
    (hd : Proves (dec a)) :
    Proves (dec (.all (.or (neg (ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ t))) a))) := by
  have hu : Proves (.all (dec a)) :=
    Relative.all_intro SetTheory.PA.Formula.Ax_s_sentences (G := []) hd
  apply dec_map ((ball_decidable t a).mp hu)
  · exact all_imp (guard_reverse a (FoundationHAOrderDecidable.lt_decidable _ _))
  · exact all_imp (guard_forward _ _)

/-- The level-zero conclusion is proved directly from the actual hierarchy
constructors, including the positive-bound condition of both bounded cases. -/
theorem hierarchy_zero_decidable {ξ : Type*} {n s : Nat} {Γ : Polarity}
    {p : Semiformula ℒₒᵣ ξ n} (hp : LO.FirstOrder.Arithmetic.Hierarchy Γ s p) (hs : s = 0)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) : Proves (dec (ordinaryAux bv fv p)) := by
  induction hp generalizing fv with
  | verum =>
    exact Relative.or_intro_left _ (Relative.imp_intro (Relative.hypothesis List.mem_cons_self))
  | falsum =>
    exact Relative.or_intro_right _ (Relative.imp_intro (Relative.hypothesis List.mem_cons_self))
  | rel _ _ r v =>
    cases r
    · exact HA.EqualityDecidable.eq_decidable _ _
    · exact FoundationHAOrderDecidable.lt_decidable _ _
  | nrel _ _ r v =>
    cases r
    · exact dec_neg (HA.EqualityDecidable.eq_decidable _ _)
    · exact dec_neg (FoundationHAOrderDecidable.lt_decidable _ _)
  | and hp hq ihp ihq => exact dec_and (ihp hs bv fv) (ihq hs bv fv)
  | or hp hq ihp ihq => exact dec_or (ihp hs bv fv) (ihq hs bv fv)
  | ball ht hp ih =>
    obtain ⟨u, hu⟩ := Rew.positive_iff.mp ht
    subst hu
    rw [ordinary_ball]
    exact guarded_all_decidable _ _ (ih hs (liftBound bv) (liftFree fv))
  | bexs ht hp ih =>
    obtain ⟨u, hu⟩ := Rew.positive_iff.mp ht
    subst hu
    rw [ordinary_bex]
    apply (bex_decidable _ _).mp
    exact Relative.all_intro SetTheory.PA.Formula.Ax_s_sentences (G := [])
      (ih hs (liftBound bv) (liftFree fv))
  | exs => cases hs
  | all => cases hs
  | sigma => cases hs
  | pi => cases hs
  | dummy_sigma => cases hs
  | dummy_pi => cases hs

/-- Genuine HA decidability of the ordinary interpretation of an actual
Foundation DeltaZero formula; no standard-model semantics is a premise. -/
theorem ordinary_decidable {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : LO.FirstOrder.Arithmetic.DeltaZero p) (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    Proves (dec (ordinaryAux bv fv p)) := hierarchy_zero_decidable hp rfl bv fv

/-- The same decision is available under any finite open assumption context. -/
theorem ordinary_decidable_relative {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : LO.FirstOrder.Arithmetic.DeltaZero p) (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (G : List SetTheory.PA.Formula) : Relative SetTheory.PA.Formula.Ax_s G
      (dec (ordinaryAux bv fv p)) := (ordinary_decidable hp bv fv).weaken (by simp)

end DiophantineConsistency.FoundationHADeltaZero
