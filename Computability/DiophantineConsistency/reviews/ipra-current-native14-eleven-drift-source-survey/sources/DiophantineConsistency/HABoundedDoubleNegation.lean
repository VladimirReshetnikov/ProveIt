import DiophantineConsistency.HABoundedQuantifiers

/-! Finite double-negation shift proved inside conventional HA.

The matrix is arbitrary and need not be decidable. The bounded witness is
its free slot zero; other free slots remain ambient parameters. The bound
term lives outside the bounded quantifier. Only actual HA formula induction
is used; no unbounded double-negation shift or existential witness recovery
is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HABoundedDoubleNegation
open SetTheory.PA HA FoundationPAHFSyntax HABoundedQuantifiers
open FoundationHAOrderAdditive

/-- Finite conjunction needs no decision or stability premise. -/
theorem doubleNeg_pair {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (ha : Relative B G (doubleNeg a)) (hb : Relative B G (doubleNeg b)) :
    Relative B G (doubleNeg (.and a b)) := by
  apply Relative.imp_intro
  apply (ha.prepend _).mp
  apply Relative.imp_intro
  apply ((hb.prepend _).prepend _).mp
  apply Relative.imp_intro
  have hn : Relative B (b :: a :: neg (.and a b) :: G) (neg (.and a b)) :=
    Relative.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact hn.mp ((Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)).and_intro
    (Relative.hypothesis List.mem_cons_self))

/-- The induction variable is an extra ambient parameter, not the bounded
witness. `plus` leaves that witness fixed while shifting the old parameters. -/
def shiftBody (a : Formula) : Formula :=
  .imp (ball (.var 0) (doubleNeg (plus a))) (doubleNeg (ball (.var 0) (plus a)))

theorem shiftBody_inst (a : Formula) (t : Term) :
    inst (shiftBody a) t = .imp (ball t (doubleNeg a)) (doubleNeg (ball t a)) := by
  simp only [inst, shiftBody, doubleNeg, neg, Formula.subst, subst_ball,
    Term.subst, Formula.instTerm, drop_parameter]

theorem shiftBody_succ (a : Formula) :
    Formula.subst Formula.substSuccVar (shiftBody a) =
      .imp (ball (.succ (.var 0)) (doubleNeg (plus a)))
        (doubleNeg (ball (.succ (.var 0)) (plus a))) := by
  have he : Formula.subst (Term.upSubst Formula.substSuccVar) (plus a) = plus a := by
    rw [plus, Formula.subst_rename, ← Formula.subst_var_rename]
    apply Formula.subst_ext
    intro n
    cases n <;> rfl
  simp only [shiftBody, doubleNeg, neg, Formula.subst, subst_ball,
    Term.subst, Formula.substSuccVar, he]

/-- This is a derivation using the actual HA formula-induction axiom. -/
theorem bounded_shift_all (a : Formula) : Proves (.all (shiftBody a)) := by
  apply Arithmetic.induction (shiftBody a)
  · rw [Formula.substZero_eq_instTerm]
    change Proves (inst (shiftBody a) .zero)
    rw [shiftBody_inst]
    apply Relative.imp_intro
    exact (relative_of_derives (Derives.doubleNeg_intro _ _)).mp
      ((ball_zero a).weaken (by simp))
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    rw [shiftBody_succ]
    apply Relative.imp_intro
    let G := [ball (.succ (.var 0)) (doubleNeg (plus a)), shiftBody a]
    have ih : Relative Formula.Ax_s G (shiftBody a) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    have hh : Relative Formula.Ax_s G (ball (.succ (.var 0)) (doubleNeg (plus a))) :=
      Relative.hypothesis List.mem_cons_self
    have hs := ((ball_succ_forward (.var 0) (doubleNeg (plus a))).weaken (by simp)).mp hh
    have hleft : Relative Formula.Ax_s G (doubleNeg (ball (.var 0) (plus a))) :=
      ih.mp hs.and_left
    have hright : Relative Formula.Ax_s G (doubleNeg (inst (plus a) (.var 0))) := by
      simpa only [inst, doubleNeg, neg, Formula.subst] using hs.and_right
    exact (map_doubleNeg ((ball_succ_reverse (.var 0) (plus a)).weaken (by simp))).mp
      (doubleNeg_pair hleft hright)

/-- Finite bounded double-negation shift, for every term and arbitrary matrix. -/
theorem bounded_doubleNeg_shift (t : Term) (a : Formula) :
    Proves (.imp (ball t (doubleNeg a)) (doubleNeg (ball t a))) := by
  have h := Relative.all_elim t (bounded_shift_all a)
  change Proves (inst (shiftBody a) t) at h
  simpa only [shiftBody_inst] using h

/-- The converse distributes a double negation over each bounded instance.
The whole assumption context is shifted when the witness is introduced. -/
theorem bounded_doubleNeg_forward (t : Term) (a : Formula) :
    Proves (.imp (doubleNeg (ball t a)) (ball t (doubleNeg a))) := by
  apply Relative.imp_intro
  apply Relative.all_intro Formula.Ax_s_sentences
  apply Relative.imp_intro
  let ts := Term.rename Nat.succ t
  let G := ltFormula (.var 0) ts ::
    [doubleNeg (ball t a)].map (Formula.rename Nat.succ)
  have hd : Relative Formula.Ax_s G (doubleNeg (ball ts (plus a))) := by
    simpa only [G, List.map_cons, List.map_nil, doubleNeg, neg, Formula.rename,
      rename_ball, plus] using
      (Relative.hypothesis (B := Formula.Ax_s) (G := G)
        (List.mem_cons_of_mem _ List.mem_cons_self))
  have hl : Relative Formula.Ax_s G (ltFormula (.var 0) ts) :=
    Relative.hypothesis List.mem_cons_self
  have hm : Relative Formula.Ax_s G (.imp (ball ts (plus a)) a) := by
    apply Relative.imp_intro
    have hb : Relative Formula.Ax_s (ball ts (plus a) :: G) (ball ts (plus a)) :=
      Relative.hypothesis List.mem_cons_self
    simpa only [inst_plus_zero] using ball_elim hb (.var 0) (hl.prepend _)
  exact (map_doubleNeg hm).mp hd

theorem bounded_doubleNeg_equivalence (t : Term) (a : Formula) :
    Proves (.and
      (.imp (ball t (doubleNeg a)) (doubleNeg (ball t a)))
      (.imp (doubleNeg (ball t a)) (ball t (doubleNeg a)))) :=
  (bounded_doubleNeg_shift t a).and_intro (bounded_doubleNeg_forward t a)

/-- Any finite open context is retained; it need not decide the matrix. -/
theorem bounded_doubleNeg_relative (t : Term) (a : Formula) (G : List Formula) :
    Relative Formula.Ax_s G (.and
      (.imp (ball t (doubleNeg a)) (doubleNeg (ball t a)))
      (.imp (doubleNeg (ball t a)) (ball t (doubleNeg a)))) :=
  (bounded_doubleNeg_equivalence t a).weaken (by simp)

end DiophantineConsistency.HABoundedDoubleNegation
