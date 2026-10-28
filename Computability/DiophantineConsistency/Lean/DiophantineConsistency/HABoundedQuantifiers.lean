import DiophantineConsistency.HAStrictIntervals

/-! Literal finite quantifiers and their decidability inside HA.

The matrix's free slot zero is its bounded witness; higher free slots are
ambient parameters. The bound term lives outside that binder. The uniform
premise is the object-language formula `all (dec a)`, not an external family
of decisions for standard numerals. The only induction is HA formula
induction, with the ambient parameters explicitly shifted under its binder.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HABoundedQuantifiers
open SetTheory.PA HA FoundationPAHFSyntax FoundationHAOrderBase HAStrictIntervals

def dec (a : Formula) : Formula := .or a (neg a)
def inst (a : Formula) (t : Term) : Formula := Formula.subst (Formula.instTerm t) a
def plus (a : Formula) : Formula := Formula.rename (SetTheory.up Nat.succ) a
def ball (t : Term) (a : Formula) : Formula :=
  .all (.imp (ltFormula (.var 0) (Term.rename Nat.succ t)) a)
def bex (t : Term) (a : Formula) : Formula :=
  .ex (.and (ltFormula (.var 0) (Term.rename Nat.succ t)) a)

theorem rename_ball (r : Nat → Nat) (t : Term) (a : Formula) :
    Formula.rename r (ball t a) = ball (Term.rename r t) (Formula.rename (SetTheory.up r) a) := by
  simp only [ball, Formula.rename, rename_ltFormula, Term.rename]
  congr 3
  rw [Term.rename_comp, Term.rename_comp]
  exact Term.rename_ext t _ _ (fun _ => rfl)

theorem rename_bex (r : Nat → Nat) (t : Term) (a : Formula) :
    Formula.rename r (bex t a) = bex (Term.rename r t) (Formula.rename (SetTheory.up r) a) := by
  simp only [bex, Formula.rename, rename_ltFormula, Term.rename]
  congr 3
  rw [Term.rename_comp, Term.rename_comp]
  exact Term.rename_ext t _ _ (fun _ => rfl)

theorem subst_ball (σ : Nat → Term) (t : Term) (a : Formula) :
    Formula.subst σ (ball t a) = ball (Term.subst σ t) (Formula.subst (Term.upSubst σ) a) := by
  simp only [ball, Formula.subst, subst_ltFormula, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem subst_bex (σ : Nat → Term) (t : Term) (a : Formula) :
    Formula.subst σ (bex t a) = bex (Term.subst σ t) (Formula.subst (Term.upSubst σ) a) := by
  simp only [bex, Formula.subst, subst_ltFormula, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem inst_plus_zero (a : Formula) : inst (plus a) (.var 0) = a :=
  Formula.subst_instTerm_var_zero_rename_up_succ a

theorem inst_plus_shift (a : Formula) (t : Term) :
    inst (plus a) (Term.rename Nat.succ t) = Formula.rename Nat.succ (inst a t) :=
  Formula.subst_instTerm_rename_up a Nat.succ t

private theorem explode {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G .bot) : Relative B G a := by
  obtain ⟨L,hL,hp⟩ := h
  exact ⟨L,hL,.botE _ _ hp⟩

theorem ball_elim {G : List Formula} {t : Term} {a : Formula}
    (h : Relative Formula.Ax_s G (ball t a)) (s : Term)
    (hl : Relative Formula.Ax_s G (ltFormula s t)) : Relative Formula.Ax_s G (inst a s) := by
  have hh := Relative.all_elim s h
  simp only [Formula.subst, subst_ltFormula, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] at hh
  exact hh.mp hl

theorem bex_intro {G : List Formula} {t s : Term} {a : Formula}
    (hl : Relative Formula.Ax_s G (ltFormula s t))
    (ha : Relative Formula.Ax_s G (inst a s)) : Relative Formula.Ax_s G (bex t a) := by
  apply Relative.ex_intro _ s
  simpa only [inst, Formula.subst, subst_ltFormula, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using hl.and_intro ha

theorem ball_zero (a : Formula) : Proves (ball .zero a) := by
  apply Relative.all_intro Formula.Ax_s_sentences (G := [])
  apply Relative.imp_intro
  exact explode (((HAStrictIntervals.not_lt_zero (.var 0)).weaken (by simp)).mp
    (Relative.hypothesis List.mem_cons_self))

theorem not_bex_zero (a : Formula) : Proves (neg (bex .zero a)) := by
  apply Relative.imp_intro
  apply Relative.ex_elim Formula.Ax_s_sentences (Relative.hypothesis List.mem_cons_self)
  exact ((HAStrictIntervals.not_lt_zero (.var 0)).weaken (by simp)).mp
    (Relative.and_left (Relative.hypothesis List.mem_cons_self))

theorem ball_succ_forward (t : Term) (a : Formula) :
    Proves (.imp (ball (.succ t) a) (.and (ball t a) (inst a t))) := by
  apply Relative.imp_intro
  apply Relative.and_intro
  · apply Relative.all_intro Formula.Ax_s_sentences
    apply Relative.imp_intro
    let ts := Term.rename Nat.succ t
    have hb : Relative Formula.Ax_s
        (ltFormula (.var 0) ts :: [ball (.succ t) a].map (Formula.rename Nat.succ))
        (ball (.succ ts) (plus a)) := by
      simpa only [List.map_cons, List.map_nil, rename_ball, Term.rename, plus]
        using (Relative.hypothesis (B := Formula.Ax_s)
          (G := [ltFormula (.var 0) ts, Formula.rename Nat.succ (ball (.succ t) a)])
          (List.mem_cons_of_mem _ List.mem_cons_self))
    have hl := lt_succ_join (Relative.or_intro_left _
      (Relative.hypothesis (B := Formula.Ax_s) (G := ltFormula (.var 0) ts ::
        [ball (.succ t) a].map (Formula.rename Nat.succ)) List.mem_cons_self))
    simpa only [inst_plus_zero] using ball_elim hb (.var 0) hl
  · exact ball_elim (Relative.hypothesis List.mem_cons_self) t
      ((lt_self_succ t).weaken (by simp))

theorem ball_succ_reverse (t : Term) (a : Formula) :
    Proves (.imp (.and (ball t a) (inst a t)) (ball (.succ t) a)) := by
  apply Relative.imp_intro
  apply Relative.all_intro Formula.Ax_s_sentences
  apply Relative.imp_intro
  let ts := Term.rename Nat.succ t
  let G := ltFormula (.var 0) (.succ ts) ::
    [.and (ball t a) (inst a t)].map (Formula.rename Nat.succ)
  have hp : Relative Formula.Ax_s G (.and (ball ts (plus a)) (inst (plus a) ts)) := by
    simpa only [G, List.map_cons, List.map_nil, Formula.rename, rename_ball,
      ← inst_plus_shift, plus] using
      (Relative.hypothesis (B := Formula.Ax_s) (G := G) (List.mem_cons_of_mem _ List.mem_cons_self))
  apply Relative.or_elim (lt_succ_split (Relative.hypothesis (G := G) List.mem_cons_self))
  · simpa only [inst_plus_zero] using ball_elim (hp.and_left.prepend _) (.var 0)
      (Relative.hypothesis List.mem_cons_self)
  · have he : Relative Formula.Ax_s (.eq (.var 0) ts :: G) (.eq (.var 0) ts) :=
      Relative.hypothesis List.mem_cons_self
    simpa only [plus, Formula.subst_instTerm_var_zero_rename_up_succ] using Relative.eq_elim (plus a) he.eq_symm (hp.and_right.prepend _)

theorem bex_succ_forward (t : Term) (a : Formula) :
    Proves (.imp (bex (.succ t) a) (.or (bex t a) (inst a t))) := by
  apply Relative.imp_intro
  apply Relative.ex_elim Formula.Ax_s_sentences (Relative.hypothesis List.mem_cons_self)
  let ts := Term.rename Nat.succ t
  let G := .and (ltFormula (.var 0) (.succ ts)) a ::
    [bex (.succ t) a].map (Formula.rename Nat.succ)
  have hp : Relative Formula.Ax_s G (.and (ltFormula (.var 0) (.succ ts)) a) :=
    Relative.hypothesis List.mem_cons_self
  change Relative Formula.Ax_s G (.or (Formula.rename Nat.succ (bex t a))
    (Formula.rename Nat.succ (inst a t)))
  rw [rename_bex, ← inst_plus_shift]
  apply Relative.or_elim (lt_succ_split hp.and_left)
  · apply Relative.or_intro_left
    apply bex_intro (s := .var 0) (Relative.hypothesis List.mem_cons_self)
    simpa only [inst, plus, Formula.subst_instTerm_var_zero_rename_up_succ] using hp.and_right.prepend (ltFormula (.var 0) ts)
  · apply Relative.or_intro_right
    have he : Relative Formula.Ax_s (.eq (.var 0) ts :: G) (.eq (.var 0) ts) :=
      Relative.hypothesis List.mem_cons_self
    apply Relative.eq_elim (plus a) he
    simpa only [inst, plus, Formula.subst_instTerm_var_zero_rename_up_succ] using hp.and_right.prepend (.eq (.var 0) ts)

theorem bex_succ_reverse (t : Term) (a : Formula) :
    Proves (.imp (.or (bex t a) (inst a t)) (bex (.succ t) a)) := by
  apply Relative.imp_intro
  apply Relative.or_elim (Relative.hypothesis List.mem_cons_self)
  · apply Relative.ex_elim Formula.Ax_s_sentences (Relative.hypothesis List.mem_cons_self)
    let ts := Term.rename Nat.succ t
    let G := .and (ltFormula (.var 0) ts) a ::
      (bex t a :: [.or (bex t a) (inst a t)]).map (Formula.rename Nat.succ)
    have hp : Relative Formula.Ax_s G (.and (ltFormula (.var 0) ts) a) :=
      Relative.hypothesis List.mem_cons_self
    rw [rename_bex]
    apply bex_intro (s := .var 0)
      (lt_succ_join (Relative.or_intro_left _ hp.and_left))
    simpa only [inst, plus, Formula.subst_instTerm_var_zero_rename_up_succ] using hp.and_right
  · exact bex_intro ((lt_self_succ t).weaken (by simp))
      (Relative.hypothesis List.mem_cons_self)

private theorem dec_map {G : List Formula} {a b : Formula}
    (hd : Relative Formula.Ax_s G (dec a))
    (hf : Relative Formula.Ax_s G (.imp a b)) (hb : Relative Formula.Ax_s G (.imp b a)) :
    Relative Formula.Ax_s G (dec b) := by
  apply Relative.or_elim hd
  · exact Relative.or_intro_left _ ((hf.prepend _).mp (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    exact ((Relative.hypothesis (B := Formula.Ax_s)
      (G := b :: neg a :: G) (List.mem_cons_of_mem _ List.mem_cons_self))).mp
      (((hb.prepend _).prepend _).mp (Relative.hypothesis List.mem_cons_self))

theorem dec_and {G : List Formula} {a b : Formula}
    (ha : Relative Formula.Ax_s G (dec a)) (hb : Relative Formula.Ax_s G (dec b)) :
    Relative Formula.Ax_s G (dec (.and a b)) := by
  apply Relative.or_elim ha
  · apply Relative.or_elim (hb.prepend a)
    · exact Relative.or_intro_left _ ((Relative.hypothesis
        (List.mem_cons_of_mem _ List.mem_cons_self)).and_intro
        (Relative.hypothesis List.mem_cons_self))
    · apply Relative.or_intro_right
      apply Relative.imp_intro
      exact (Relative.hypothesis (G := .and a b :: neg b :: a :: G)
        (List.mem_cons_of_mem _ List.mem_cons_self)).mp
        (Relative.and_right (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_intro_right
    apply Relative.imp_intro
    exact (Relative.hypothesis (G := .and a b :: neg a :: G)
      (List.mem_cons_of_mem _ List.mem_cons_self)).mp
      (Relative.and_left (Relative.hypothesis List.mem_cons_self))

theorem dec_or {G : List Formula} {a b : Formula}
    (ha : Relative Formula.Ax_s G (dec a)) (hb : Relative Formula.Ax_s G (dec b)) :
    Relative Formula.Ax_s G (dec (.or a b)) := by
  apply Relative.or_elim ha
  · exact Relative.or_intro_left _ (Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self))
  · apply Relative.or_elim (hb.prepend (neg a))
    · exact Relative.or_intro_left _ (Relative.or_intro_right _ (Relative.hypothesis List.mem_cons_self))
    · apply Relative.or_intro_right
      apply Relative.imp_intro
      apply Relative.or_elim (Relative.hypothesis List.mem_cons_self)
      · exact (Relative.hypothesis (G := a :: .or a b :: neg b :: neg a :: G)
          (by simp [neg])).mp (Relative.hypothesis List.mem_cons_self)
      · exact (Relative.hypothesis (G := b :: .or a b :: neg b :: neg a :: G)
          (by simp [neg])).mp (Relative.hypothesis List.mem_cons_self)

def decisionBody (a : Formula) : Formula :=
  .and (dec (ball (.var 0) (plus a))) (dec (bex (.var 0) (plus a)))

theorem drop_parameter (a : Formula) (t : Term) :
    Formula.subst (Term.upSubst (Formula.instTerm t)) (plus a) = a := by
  rw [plus, Formula.subst_rename]
  calc
    _ = Formula.subst (fun n => Term.var n) a := by
      apply Formula.subst_ext
      intro n
      cases n <;> rfl
    _ = a := Formula.subst_id a

theorem decisionBody_inst (a : Formula) (t : Term) :
    inst (decisionBody a) t = .and (dec (ball t a)) (dec (bex t a)) := by
  simp only [inst, decisionBody, dec, neg, Formula.subst, subst_ball, subst_bex,
    Term.subst, Formula.instTerm, drop_parameter]

theorem decisionBody_succ (a : Formula) :
    Formula.subst Formula.substSuccVar (decisionBody a) =
      .and (dec (ball (.succ (.var 0)) (plus a))) (dec (bex (.succ (.var 0)) (plus a))) := by
  have he : Formula.subst (Term.upSubst Formula.substSuccVar) (plus a) = plus a := by
    rw [plus, Formula.subst_rename, ← Formula.subst_var_rename]
    apply Formula.subst_ext
    intro n
    cases n <;> rfl
  simp only [decisionBody, dec, neg, Formula.subst, subst_ball, subst_bex,
    Term.subst, Formula.substSuccVar, he]

/-- Actual formula induction, under the one uniform object-language premise. -/
theorem decisions_all (a : Formula) :
    Relative Formula.Ax_s [.all (dec a)] (.all (decisionBody a)) := by
  apply Arithmetic.induction (decisionBody a)
  · rw [Formula.substZero_eq_instTerm]
    change Relative Formula.Ax_s _ (inst (decisionBody a) .zero)
    rw [decisionBody_inst]
    exact (Relative.or_intro_left _ ((ball_zero a).weaken (by simp))).and_intro
      (Relative.or_intro_right _ ((not_bex_zero a).weaken (by simp)))
  · apply Relative.all_intro Formula.Ax_s_sentences
    apply Relative.imp_intro
    rw [decisionBody_succ]
    let G := decisionBody a :: [.all (dec a)].map (Formula.rename Nat.succ)
    have ih : Relative Formula.Ax_s G (decisionBody a) := Relative.hypothesis List.mem_cons_self
    have hd : Relative Formula.Ax_s G (dec a) := by
      have hu : Relative Formula.Ax_s G (.all (dec (plus a))) :=
        Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
      have hh := Relative.all_elim (.var 0) hu
      simpa only [dec, neg, Formula.subst, plus,
        Formula.subst_instTerm_var_zero_rename_up_succ] using hh
    have hd' : Relative Formula.Ax_s G (dec (inst (plus a) (.var 0))) := by
      simpa only [inst_plus_zero] using hd
    exact (dec_map (dec_and ih.and_left hd')
      ((ball_succ_reverse (.var 0) (plus a)).weaken (by simp))
      ((ball_succ_forward (.var 0) (plus a)).weaken (by simp))).and_intro
      (dec_map (dec_or ih.and_right hd')
        ((bex_succ_reverse (.var 0) (plus a)).weaken (by simp))
        ((bex_succ_forward (.var 0) (plus a)).weaken (by simp)))

theorem ball_decidable (t : Term) (a : Formula) :
    Proves (.imp (.all (dec a)) (dec (ball t a))) := by
  apply Relative.imp_intro
  have h := Relative.all_elim t (decisions_all a)
  change Relative Formula.Ax_s _ (inst (decisionBody a) t) at h
  rw [decisionBody_inst] at h
  exact h.and_left

theorem bex_decidable (t : Term) (a : Formula) :
    Proves (.imp (.all (dec a)) (dec (bex t a))) := by
  apply Relative.imp_intro
  have h := Relative.all_elim t (decisions_all a)
  change Relative Formula.Ax_s _ (inst (decisionBody a) t) at h
  rw [decisionBody_inst] at h
  exact h.and_right

end DiophantineConsistency.HABoundedQuantifiers
