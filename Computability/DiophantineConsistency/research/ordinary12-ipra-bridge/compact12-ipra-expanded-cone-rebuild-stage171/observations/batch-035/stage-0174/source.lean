import DiophantineConsistency.FoundationHADeltaZeroGG
import DiophantineConsistency.HABoundedDoubleNegation

/-! Actual hierarchy-one formulas compared inside conventional HA.

The ordinary formula remains double-negated. This is an induction on the
existing Foundation hierarchy predicate, not a new GG algorithm or grammar.
Only bounded universality uses finite DNS. No existential witness is
recovered from a double negation, and no fixed checker is normalized here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHASigmaOneGG
open LO LO.FirstOrder
open HA FoundationPAHFSyntax HABoundedQuantifiers FoundationHADeltaZero
open FoundationHADeltaZeroGG HABoundedDoubleNegation FoundationHAOrderAdditive
open scoped LO.FirstOrder

private theorem refl (a : F) : ProofEquiv a a :=
  (HA.proves_identity a).and_intro (HA.proves_identity a)

private theorem swap {a b : F} (h : ProofEquiv a b) : ProofEquiv b a :=
  h.and_right.and_intro h.and_left

private theorem trans {a b c : F} (h : ProofEquiv a b) (k : ProofEquiv b c) :
    ProofEquiv a c :=
  (h.and_left.imp_trans k.and_left).and_intro (k.and_right.imp_trans h.and_right)

private theorem dn_map {a b : F} (h : ProofEquiv a b) :
    ProofEquiv (doubleNeg a) (doubleNeg b) :=
  (map_doubleNeg h.and_left).and_intro (map_doubleNeg h.and_right)

private theorem contra {a b : F} (h : Proves (.imp a b)) :
    Proves (.imp (neg b) (neg a)) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  exact (Relative.hypothesis (G := [a, neg b])
    (List.mem_cons_of_mem _ List.mem_cons_self)).mp
    ((h.weaken (by simp)).mp (Relative.hypothesis List.mem_cons_self))

private theorem neg_map {a b : F} (h : ProofEquiv a b) : ProofEquiv (neg a) (neg b) :=
  (contra h.and_right).and_intro (contra h.and_left)

private theorem all_map {a b : F} (h : ProofEquiv a b) : ProofEquiv (.all a) (.all b) :=
  (all_imp h.and_left).and_intro (all_imp h.and_right)

private theorem and_imp {a b c d : F} (h : Proves (.imp a c)) (k : Proves (.imp b d)) :
    Proves (.imp (.and a b) (.and c d)) := by
  apply Relative.imp_intro
  exact ((h.prepend _).mp (Relative.and_left (Relative.hypothesis List.mem_cons_self))).and_intro
    ((k.prepend _).mp (Relative.and_right (Relative.hypothesis List.mem_cons_self)))

private theorem and_map {a b c d : F} (h : ProofEquiv a c) (k : ProofEquiv b d) :
    ProofEquiv (.and a b) (.and c d) :=
  (and_imp h.and_left k.and_left).and_intro (and_imp h.and_right k.and_right)

theorem negative_doubleNeg {a : F} (ha : Negative a) : ProofEquiv a (doubleNeg a) :=
  (Proves.of_derives (Derives.doubleNeg_intro [] a)).and_intro ha.proves_stability

/-- Negations are compared without stability of the original matrix. -/
theorem neg_of_doubleNeg_equiv {a c : F} (h : ProofEquiv c (doubleNeg a)) :
    ProofEquiv (neg c) (neg a) :=
  trans (neg_map h) (swap (negative_doubleNeg (.neg a)))

/-- Double negation distributes over a finite conjunction intuitionistically. -/
theorem and_doubleNeg_equiv {a b c d : F} (h : ProofEquiv c (doubleNeg a))
    (k : ProofEquiv d (doubleNeg b)) :
    ProofEquiv (.and c d) (doubleNeg (.and a b)) := by
  apply Relative.and_intro
  · apply Relative.imp_intro
    exact doubleNeg_pair
      ((h.and_left.prepend _).mp (Relative.and_left (Relative.hypothesis List.mem_cons_self)))
      ((k.and_left.prepend _).mp (Relative.and_right (Relative.hypothesis List.mem_cons_self)))
  · have hl : Proves (.imp (.and a b) a) :=
      .of_derives (Derives.and_left [] a b)
    have hr : Proves (.imp (.and a b) b) :=
      .of_derives (Derives.and_right [] a b)
    apply Relative.imp_intro
    exact ((h.and_right.prepend _).mp
      (((map_doubleNeg hl).prepend _).mp (Relative.hypothesis List.mem_cons_self))).and_intro
      ((k.and_right.prepend _).mp
        (((map_doubleNeg hr).prepend _).mp (Relative.hypothesis List.mem_cons_self)))

private theorem not_or (a b : F) : ProofEquiv (neg (.or a b)) (.and (neg a) (neg b)) := by
  apply Relative.and_intro
  · apply Relative.imp_intro
    apply Relative.and_intro
    · apply Relative.imp_intro
      exact (Relative.hypothesis (G := [a, neg (.or a b)])
        (List.mem_cons_of_mem _ List.mem_cons_self)).mp
        (Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self))
    · apply Relative.imp_intro
      exact (Relative.hypothesis (G := [b, neg (.or a b)])
        (List.mem_cons_of_mem _ List.mem_cons_self)).mp
        (Relative.or_intro_right _ (Relative.hypothesis List.mem_cons_self))
  · apply Relative.imp_intro
    apply Relative.imp_intro
    apply Relative.or_elim (Relative.hypothesis List.mem_cons_self)
    · exact (Relative.and_left (Relative.hypothesis (a := .and (neg a) (neg b))
        (G := [a, .or a b, .and (neg a) (neg b)])
        (by simp))).mp (Relative.hypothesis List.mem_cons_self)
    · exact (Relative.and_right (Relative.hypothesis (a := .and (neg a) (neg b))
        (G := [b, .or a b, .and (neg a) (neg b)])
        (by simp))).mp (Relative.hypothesis List.mem_cons_self)

/-- Literal GG disjunction yields only double-negated ordinary disjunction. -/
theorem or_doubleNeg_equiv {a b c d : F} (h : ProofEquiv c (doubleNeg a))
    (k : ProofEquiv d (doubleNeg b)) :
    ProofEquiv (neg (.and (neg c) (neg d))) (doubleNeg (.or a b)) :=
  trans (neg_map (and_map (neg_of_doubleNeg_equiv h) (neg_of_doubleNeg_equiv k)))
    (swap (neg_map (not_or a b)))

private theorem not_ex (a : F) : ProofEquiv (neg (.ex a)) (.all (neg a)) := by
  apply Relative.and_intro (not_ex_all_not a)
  apply Relative.imp_intro
  apply Relative.imp_intro
  exact (((encoded_ex_forward (HA.proves_identity a)).weaken (by simp)).mp
    (Relative.hypothesis List.mem_cons_self)).mp
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The quantified negative comparison keeps the whole context shifted in
the accepted `not_ex_all_not` and `encoded_ex_forward` derivations. -/
theorem ex_doubleNeg_equiv {a c : F} (h : ProofEquiv c (doubleNeg a)) :
    ProofEquiv (neg (.all (neg c))) (doubleNeg (.ex a)) :=
  trans (neg_map (all_map (neg_of_doubleNeg_equiv h))) (swap (neg_map (not_ex a)))

/-- Exact source bounded-all guard. Neither the matrix nor this guard is
assumed decidable for this finite logical implication. -/
theorem guard_doubleNeg_equiv {l a c : F} (h : ProofEquiv c (doubleNeg a)) :
    ProofEquiv (neg (.and (doubleNeg l) (neg c))) (.imp l (doubleNeg a)) := by
  let hn := neg_of_doubleNeg_equiv h
  apply Relative.and_intro
  · apply Relative.imp_intro
    apply Relative.imp_intro
    apply Relative.imp_intro
    let G : List F := [neg a, l, neg (.and (doubleNeg l) (neg c))]
    have hl : Relative SetTheory.PA.Formula.Ax_s G l :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    have hnl : Relative SetTheory.PA.Formula.Ax_s G (doubleNeg l) :=
      (relative_of_derives (Derives.doubleNeg_intro _ _)).mp hl
    have hnc : Relative SetTheory.PA.Formula.Ax_s G (neg c) :=
      (hn.and_right.weaken (by simp [G])).mp (Relative.hypothesis List.mem_cons_self)
    exact (Relative.hypothesis (G := G) (by simp [G, neg])).mp (hnl.and_intro hnc)
  · apply Relative.imp_intro
    apply Relative.imp_intro
    let G : List F := [.and (doubleNeg l) (neg c), .imp l (doubleNeg a)]
    have hp : Relative SetTheory.PA.Formula.Ax_s G (.and (doubleNeg l) (neg c)) :=
      Relative.hypothesis List.mem_cons_self
    apply hp.and_left.mp
    apply Relative.imp_intro
    have hna := ((hn.and_left.weaken (by simp [G])).mp hp.and_right).prepend l
    exact ((Relative.hypothesis (a := .imp l (doubleNeg a)) (G := l :: G) (by simp [G])).mp
      (Relative.hypothesis List.mem_cons_self)).mp hna

private theorem bounded_all_equiv (t : PTerm) {a c : F}
    (h : ProofEquiv c (doubleNeg a)) :
    ProofEquiv
      (.all (neg (.and (doubleNeg (ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ t)))
        (neg c))))
      (doubleNeg (.all (.or (neg (ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ t))) a))) := by
  let l := ltFormula (.var 0) (SetTheory.PA.Term.rename Nat.succ t)
  have hg : ProofEquiv (.all (.or (neg l) a)) (ball t a) :=
    all_map ((guard_forward l a).and_intro
      (guard_reverse a (FoundationHAOrderDecidable.lt_decidable _ _)))
  exact trans (all_map (guard_doubleNeg_equiv h))
    (trans (bounded_doubleNeg_equivalence t a) (dn_map (swap hg)))

private theorem zero_doubleNeg {ξ : Type*} {n s : Nat} {Γ : Polarity}
    {p : Semiformula ℒₒᵣ ξ n} (hp : Arithmetic.Hierarchy Γ s p) (hs : s = 0)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)) :=
  trans (swap (hierarchy_zero_equivalence hp hs bv fv))
    ((Proves.of_derives (Derives.doubleNeg_intro [] _)).and_intro
      (stable_of_decidable (hierarchy_zero_decidable hp hs bv fv)))

/-- The exact source polarity and level remain in the induction motive.
The Π0 body of `sigma` uses only the accepted bounded decision theorem. -/
theorem hierarchy_sigma_one_doubleNeg {ξ : Type*} {n s : Nat} {Γ : Polarity}
    {p : Semiformula ℒₒᵣ ξ n} (hp : Arithmetic.Hierarchy Γ s p) (hΓ : Γ = 𝚺) (hs : s = 1)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)) := by
  induction hp generalizing fv with
  | verum => exact negative_doubleNeg (.neg _)
  | falsum => exact negative_doubleNeg .bot
  | rel _ _ r v => cases r <;> exact refl _
  | nrel _ _ r v => cases r <;> exact negative_doubleNeg (.neg _)
  | and hp hq ihp ihq => exact and_doubleNeg_equiv (ihp hΓ hs bv fv) (ihq hΓ hs bv fv)
  | or hp hq ihp ihq => exact or_doubleNeg_equiv (ihp hΓ hs bv fv) (ihq hΓ hs bv fv)
  | ball ht hp ih =>
    obtain ⟨u, hu⟩ := Rew.positive_iff.mp ht
    subst hu
    rw [ordinary_ball]
    change ProofEquiv
      (.all (neg (.and (doubleNeg (ltFormula (.var 0)
        (termAux (liftBound bv) (liftFree fv) (Rew.bShift u))))
        (neg (formulaAux (liftBound bv) (liftFree fv) _))))) _
    rw [termAux_bShift]
    exact bounded_all_equiv _ (ih hΓ hs (liftBound bv) (liftFree fv))
  | bexs ht hp ih =>
    exact ex_doubleNeg_equiv (and_doubleNeg_equiv (refl _)
      (ih hΓ hs (liftBound bv) (liftFree fv)))
  | exs hp ih => exact ex_doubleNeg_equiv (ih rfl hs (liftBound bv) (liftFree fv))
  | all => cases hΓ
  | sigma hp ih =>
    exact ex_doubleNeg_equiv (zero_doubleNeg hp (by omega) (liftBound bv) (liftFree fv))
  | pi => cases hΓ
  | dummy_sigma => omega
  | dummy_pi => cases hΓ

/-- Literal existing GG image of an actual Σ1 formula, with arbitrary term
environments, compared to the double negation of its ordinary interpretation. -/
theorem sigma_one_doubleNeg {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : Arithmetic.Hierarchy 𝚺 1 p) (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    ProofEquiv (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)) :=
  hierarchy_sigma_one_doubleNeg hp rfl rfl bv fv

theorem sigma_one_doubleNeg_relative {ξ : Type*} {n : Nat} {p : Semiformula ℒₒᵣ ξ n}
    (hp : Arithmetic.Hierarchy 𝚺 1 p) (bv : Fin n → PTerm) (fv : ξ → PTerm) (G : List F) :
    Relative SetTheory.PA.Formula.Ax_s G
      (.and (.imp (formulaAux bv fv pᴺ) (doubleNeg (ordinaryAux bv fv p)))
        (.imp (doubleNeg (ordinaryAux bv fv p)) (formulaAux bv fv pᴺ))) :=
  (sigma_one_doubleNeg hp bv fv).weaken (by simp)

end DiophantineConsistency.FoundationHASigmaOneGG
