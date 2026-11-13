import DiophantineConsistency.FoundationHADeltaZero

/-! Actual bounded formulas agree with Foundation's existing GG translation
inside HA. This is not a new negative-translation algorithm. The reverse
existential step explicitly requires the HA decision of that existential,
provided only for the actual bounded source constructor below.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHADeltaZeroGG
open LO LO.FirstOrder
open HA FoundationPAHFSyntax HABoundedQuantifiers FoundationHADeltaZero
open scoped LO.FirstOrder
abbrev F := SetTheory.PA.Formula
abbrev ProofEquiv (a b : F) : Prop := Proves (.and (.imp a b) (.imp b a))

private theorem explode {G : List F} {a : F} (h : Relative SetTheory.PA.Formula.Ax_s G .bot) :
    Relative SetTheory.PA.Formula.Ax_s G a := by
  obtain ⟨L,hL,hp⟩ := h
  exact ⟨L,hL,.botE _ _ hp⟩

private theorem identity (a : F) : ProofEquiv a a :=
  (HA.proves_identity a).and_intro (HA.proves_identity a)

/-- Only an actual HA decision permits this double-negation elimination. -/
theorem stable_of_decidable {a : F} (hd : Proves (dec a)) :
    Proves (.imp (doubleNeg a) a) := by
  apply Relative.imp_intro
  apply Relative.or_elim (hd.prepend _)
  · exact Relative.hypothesis List.mem_cons_self
  · exact explode ((Relative.hypothesis (G := [neg a, doubleNeg a])
      (List.mem_cons_of_mem _ List.mem_cons_self)).mp
      (Relative.hypothesis List.mem_cons_self))

private theorem doubleNeg_equivalence {a : F} (hd : Proves (dec a)) :
    ProofEquiv a (doubleNeg a) :=
  (Proves.of_derives (Derives.doubleNeg_intro [] a)).and_intro (stable_of_decidable hd)

private theorem contrapositive {a b : F} (h : Proves (.imp a b)) :
    Proves (.imp (neg b) (neg a)) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  exact (Relative.hypothesis (G := [a,neg b])
    (List.mem_cons_of_mem _ List.mem_cons_self)).mp
    (((h.prepend _).prepend _).mp (Relative.hypothesis List.mem_cons_self))

private theorem neg_decidable {a : F} (hd : Proves (dec a)) : Proves (dec (neg a)) := by
  apply Relative.or_elim hd
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    exact (Relative.hypothesis List.mem_cons_self).mp
      (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)

private theorem and_imp {a b c d : F} (hac : Proves (.imp a c))
    (hbd : Proves (.imp b d)) : Proves (.imp (.and a b) (.and c d)) := by
  apply Relative.imp_intro
  exact ((hac.prepend _).mp (Relative.and_left (Relative.hypothesis List.mem_cons_self))).and_intro
    ((hbd.prepend _).mp (Relative.and_right (Relative.hypothesis List.mem_cons_self)))

private theorem and_equivalence {a b c d : F} (hac : ProofEquiv a c)
    (hbd : ProofEquiv b d) : ProofEquiv (.and a b) (.and c d) :=
  (and_imp hac.and_left hbd.and_left).and_intro (and_imp hac.and_right hbd.and_right)

/-- Literal negative disjunction, recovered by the two actual ordinary decisions. -/
theorem encoded_or_equivalence {a b c d : F} (hac : ProofEquiv a c)
    (hbd : ProofEquiv b d) (ha : Proves (dec a)) (hb : Proves (dec b)) :
    ProofEquiv (.or a b) (neg (.and (neg c) (neg d))) := by
  apply Relative.and_intro
  · apply Relative.imp_intro
    apply Relative.imp_intro
    apply Relative.or_elim (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact (Relative.and_left (Relative.hypothesis
        (G := [a, .and (neg c) (neg d), .or a b])
        (List.mem_cons_of_mem _ List.mem_cons_self))).mp
        ((hac.and_left.weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self))
    · exact (Relative.and_right (Relative.hypothesis
        (G := [b, .and (neg c) (neg d), .or a b])
        (List.mem_cons_of_mem _ List.mem_cons_self))).mp
        ((hbd.and_left.weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self))
  · apply Relative.imp_intro
    apply Relative.or_elim (ha.prepend _)
    · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)
    · apply Relative.or_elim (hb.weaken (by simp))
      · exact Relative.or_intro_right _ (Relative.hypothesis List.mem_cons_self)
      · have hc : Relative SetTheory.PA.Formula.Ax_s [neg b,neg a,neg (.and (neg c) (neg d))] (neg c) :=
          ((contrapositive hac.and_right).weaken (by simp)).mp
            (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        have hd : Relative SetTheory.PA.Formula.Ax_s [neg b,neg a,neg (.and (neg c) (neg d))] (neg d) :=
          ((contrapositive hbd.and_right).weaken (by simp)).mp
            (Relative.hypothesis List.mem_cons_self)
        exact explode ((Relative.hypothesis (G := [neg b,neg a,neg (.and (neg c) (neg d))])
          (by simp [neg])).mp (hc.and_intro hd))

private theorem all_equivalence {a b : F} (h : ProofEquiv a b) :
    ProofEquiv (.all a) (.all b) :=
  (all_imp h.and_left).and_intro (all_imp h.and_right)

/-- The forward existential encoding needs no decision or stability assumption. -/
theorem encoded_ex_forward {a b : F} (h : Proves (.imp a b)) :
    Proves (.imp (.ex a) (neg (.all (neg b)))) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  apply Relative.ex_elim SetTheory.PA.Formula.Ax_s_sentences
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  have hall : Relative SetTheory.PA.Formula.Ax_s
      (a :: [.all (neg b), .ex a].map (SetTheory.PA.Formula.rename Nat.succ))
      (SetTheory.PA.Formula.rename Nat.succ (.all (neg b))) :=
    Relative.hypothesis (List.mem_cons_of_mem _ (by simp))
  have hn := Relative.all_elim (.var 0) hall
  have hn' : Relative SetTheory.PA.Formula.Ax_s
      (a :: [.all (neg b), .ex a].map (SetTheory.PA.Formula.rename Nat.succ)) (neg b) := by
    simpa only [SetTheory.PA.Formula.rename, SetTheory.PA.Formula.subst_instTerm_var_zero_rename_up_succ] using hn
  exact hn'.mp ((h.weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self))

/-- An intuitionistic quantifier law with the entire context shifted. -/
theorem not_ex_all_not (a : F) : Proves (.imp (neg (.ex a)) (.all (neg a))) := by
  apply Relative.imp_intro
  apply Relative.all_intro SetTheory.PA.Formula.Ax_s_sentences
  apply Relative.imp_intro
  have hex : Relative SetTheory.PA.Formula.Ax_s (a :: [neg (.ex a)].map (SetTheory.PA.Formula.rename Nat.succ))
      (SetTheory.PA.Formula.rename Nat.succ (.ex a)) := by
    apply Relative.ex_intro _ (.var 0)
    simpa only [SetTheory.PA.Formula.rename, SetTheory.PA.Formula.subst_instTerm_var_zero_rename_up_succ] using
      (Relative.hypothesis (B := SetTheory.PA.Formula.Ax_s)
        (G := a :: [neg (.ex a)].map (SetTheory.PA.Formula.rename Nat.succ)) List.mem_cons_self)
  exact (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)).mp hex

/-- Reverse encoding is conditional on the ordinary existential's HA decision,
not on decidability of its individual instances alone. -/
theorem encoded_ex_equivalence {a b : F} (h : ProofEquiv a b)
    (hd : Proves (dec (.ex a))) : ProofEquiv (.ex a) (neg (.all (neg b))) := by
  apply Relative.and_intro (encoded_ex_forward h.and_left)
  apply Relative.imp_intro
  apply ((stable_of_decidable hd).prepend _).mp
  apply Relative.imp_intro
  have hn : Relative SetTheory.PA.Formula.Ax_s [neg (.ex a), neg (.all (neg b))] (.all (neg a)) :=
    ((not_ex_all_not a).weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self)
  have hn' := ((all_imp (contrapositive h.and_right)).weaken (by simp)).mp hn
  exact (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)).mp hn'

/-- Exact source GG recursion is used only through its existing definition.
The induction below is over the existing arithmetic hierarchy proof. -/
theorem hierarchy_zero_equivalence {ξ : Type*} {n s : Nat} {Γ : Polarity}
    {p : Semiformula ℒₒᵣ ξ n} (hp : LO.FirstOrder.Arithmetic.Hierarchy Γ s p) (hs : s=0)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    ProofEquiv (ordinaryAux bv fv p) (formulaAux bv fv pᴺ) := by
  induction hp generalizing fv with
  | verum => exact identity _
  | falsum => exact identity _
  | rel _ _ r v =>
    cases r
    · exact doubleNeg_equivalence (HA.EqualityDecidable.eq_decidable _ _)
    · exact doubleNeg_equivalence (FoundationHAOrderDecidable.lt_decidable _ _)
  | nrel _ _ r v => cases r <;> exact identity _
  | and hp hq ihp ihq => exact and_equivalence (ihp hs bv fv) (ihq hs bv fv)
  | or hp hq ihp ihq =>
    exact encoded_or_equivalence (ihp hs bv fv) (ihq hs bv fv)
      (hierarchy_zero_decidable hp hs bv fv) (hierarchy_zero_decidable hq hs bv fv)
  | ball ht hp ih =>
    apply all_equivalence
    apply encoded_or_equivalence (identity _) (ih hs (liftBound bv) (liftFree fv))
    · exact neg_decidable (FoundationHAOrderDecidable.lt_decidable _ _)
    · exact hierarchy_zero_decidable hp hs (liftBound bv) (liftFree fv)
  | bexs ht hp ih =>
    apply encoded_ex_equivalence
    · exact and_equivalence
        (doubleNeg_equivalence (FoundationHAOrderDecidable.lt_decidable _ _))
        (ih hs (liftBound bv) (liftFree fv))
    · exact hierarchy_zero_decidable (.bexs ht hp) hs bv fv
  | exs => cases hs
  | all => cases hs
  | sigma => cases hs
  | pi => cases hs
  | dummy_sigma => cases hs
  | dummy_pi => cases hs

/-- Ordinary bounded interpretation and the literal existing Foundation GG
image have actual HA proofs in both directions, for arbitrary environments. -/
theorem ordinary_gg_equivalence {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : LO.FirstOrder.Arithmetic.DeltaZero p) (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    Proves (.and (.imp (ordinaryAux bv fv p) (formulaAux bv fv pᴺ))
      (.imp (formulaAux bv fv pᴺ) (ordinaryAux bv fv p))) :=
  hierarchy_zero_equivalence hp rfl bv fv

/-- The derived comparison remains usable in any finite open context. -/
theorem ordinary_gg_equivalence_relative {ξ : Type*} {n : Nat}
    {p : Semiformula ℒₒᵣ ξ n} (hp : LO.FirstOrder.Arithmetic.DeltaZero p)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) (G : List F) :
    Relative SetTheory.PA.Formula.Ax_s G (.and (.imp (ordinaryAux bv fv p) (formulaAux bv fv pᴺ))
      (.imp (formulaAux bv fv pᴺ) (ordinaryAux bv fv p))) :=
  (ordinary_gg_equivalence hp bv fv).weaken (by simp)

end DiophantineConsistency.FoundationHADeltaZeroGG
