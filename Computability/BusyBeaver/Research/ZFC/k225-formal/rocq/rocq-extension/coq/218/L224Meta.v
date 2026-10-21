(** Copy of rocq224/src/L224Meta.v (SHA256 0707b713e1a169ffbb36085ab6c42f1c808ebdfbb9ba24cc4b715d3025fa11f8) under namespace K218F. *)
(** * L224Meta: pure-logic metatheory for [lprov224], adapted from Jeff's ZF/stdzf L1_LMeta.v.

    The derived rules and the deduction theorem are Jeff's, renamed. Equality reflexivity is
    bootstrapped from the helper (binder [wel x x]). Vacuous generalization holds for formulas
    without equality atoms, and Leibniz substitution, specialization and alphabetic variance for
    quantifier-free membership matrices; these are the instances the equality interpretation
    needs. The syntax functions [rv], [ren], [occ], [bnd] and their lemmas are Jeff's. *)
From Stdlib Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta.
From K230S Require Import KCode230.
From K218F Require Import L224Def L224Prop.
Import ListNotations.

(** ** Derived rules *)
Lemma msyl a b c : lprov224 (Wim a b) -> lprov224 (Wim b c) -> lprov224 (Wim a c).
Proof. intros H1 H2. exact (MDET _ _ (MDET _ _ (MB1 a b c) H1) H2). Qed.

Lemma mcontra a b : lprov224 (Wim a b) -> lprov224 (Wim (Wn b) (Wn a)).
Proof. intro H. exact (MDET _ _ (mlpc_contra a b) H). Qed.

Lemma mal x a b : lprov224 (Wim a b) -> lprov224 (Wim (Wal x a) (Wal x b)).
Proof. intro H. exact (MDET _ _ (MB4 x a b) (MGEN x _ H)). Qed.

Lemma mex x a b : lprov224 (Wim a b) -> lprov224 (Wim (Wex x a) (Wex x b)).
Proof. intro H. unfold Wex. apply mcontra, mal, mcontra, H. Qed.

(** ** Deduction theorem (propositional, no GEN under hypotheses) *)
Inductive mder (G : list wff) : wff -> Prop :=
  | mhyp a : In a G -> mder G a
  | mthm a : lprov224 a -> mder G a
  | mmpr a b : mder G (Wim a b) -> mder G a -> mder G b.

Lemma mruleS G h a b : mder G (Wim h (Wim a b)) -> mder G (Wim h a) -> mder G (Wim h b).
Proof.
  intros H1 H2.
  assert (H3 : mder G (Wim a (Wim h b))) by exact (mmpr _ _ _ (mthm _ _ (mlpc_C h a b)) H1).
  assert (H4 : mder G (Wim h (Wim h b))).
  { exact (mmpr _ _ _ (mmpr _ _ _ (mthm _ _ (MB1 h a (Wim h b))) H2) H3). }
  exact (mmpr _ _ _ (mthm _ _ (mlpc_W h b)) H4).
Qed.

Lemma mded G h a : mder (h :: G) a -> mder G (Wim h a).
Proof.
  induction 1 as [a [<-|Ha] | a Ha | a b _ IH1 _ IH2].
  - apply mthm, mlpc_id.
  - exact (mmpr _ _ _ (mthm _ _ (mlpc_K a h)) (mhyp _ _ Ha)).
  - exact (mmpr _ _ _ (mthm _ _ (mlpc_K a h)) (mthm _ _ Ha)).
  - exact (mruleS _ _ _ _ IH1 IH2).
Qed.

Lemma mder_lprov a : mder [] a -> lprov224 a.
Proof. induction 1 as [a []| |]; [assumption | exact (MDET _ _ IHmder1 IHmder2)]. Qed.

Ltac mdh := apply mhyp; simpl; tauto.
Ltac mdt H := apply mthm; exact H.
Ltac mmp a := apply (mmpr _ a).

(** Conjunction inside derivations ([Wa a b = -. (a -> -. b)]). *)
Lemma mder_andl G a b : mder G (Wa a b) -> mder G a.
Proof. intro H. mmp (Wa a b); [mdt (mlpc_andl a b) | exact H]. Qed.

Lemma mder_andr G a b : mder G (Wa a b) -> mder G b.
Proof. intro H. mmp (Wa a b); [mdt (mlpc_andr a b) | exact H]. Qed.

Lemma mder_andi G a b : mder G a -> mder G b -> mder G (Wa a b).
Proof. intros Ha Hb. mmp b; [mmp a; [mdt (mlpc_andi a b) | exact Ha] | exact Hb]. Qed.

(** ** Equality: reflexivity from the helper, then symmetry and transport *)
Lemma meq_refl x : lprov224 (Weq x x).
Proof.
  set (z := wel x x).
  assert (h3 : lprov224 (Wim (Weq z x) (Weq x x))) by exact (MDET _ _ (mlpc_W _ _) (MB8a z x x)).
  pose proof (MB6h x x) as h5.
  pose proof (mex z _ _ (msyl _ _ _ h3 h5)) as h7.
  exact (MDET _ _ (MB6c z (Weq x x)) (MDET _ _ h7 (MB7 z x))).
Qed.

Lemma meq_sym x y : lprov224 (Wim (Weq x y) (Weq y x)).
Proof.
  apply mder_lprov, mded. mmp (Weq x x); [mmp (Weq x y); [mdt (MB8a x y x) | mdh] | mdt (meq_refl x)].
Qed.

Lemma meq_tr_el u u' v v' : lprov224 (Wim (Weq u u') (Wim (Weq v v') (Wim (Wel u v) (Wel u' v')))).
Proof.
  apply mder_lprov, mded, mded, mded.
  mmp (Wel u' v).
  - mmp (Weq v v'); [mdt (MB8c v v' u') | mdh].
  - mmp (Wel u v); [mmp (Weq u u'); [mdt (MB8b u u' v) | mdh] | mdh].
Qed.

(** ** Formula classes *)
Fixpoint noeq (a : wff) : bool :=
  match a with
  | Weq _ _ => false
  | Wel _ _ => true
  | Wim a b => noeq a && noeq b
  | Wn a => noeq a
  | Wal _ a => noeq a
  end.

(** quantifier-free membership matrices *)
Fixpoint qfm (a : wff) : bool :=
  match a with
  | Weq _ _ | Wal _ _ => false
  | Wel _ _ => true
  | Wim a b => qfm a && qfm b
  | Wn a => qfm a
  end.

Lemma qfm_noeq a : qfm a = true -> noeq a = true.
Proof.
  induction a; simpl; intro H; try discriminate; try reflexivity; [|exact (IHa H)].
  apply andb_true_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
Qed.

Lemma qfm_bnd x a : qfm a = true -> bnd x a = false.
Proof.
  induction a; simpl; intro H; try discriminate; try reflexivity; [|exact (IHa H)].
  apply andb_true_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
Qed.

Lemma qfm_ren x y a : qfm a = true -> qfm (ren x y a) = true.
Proof.
  induction a; simpl; intro H; try discriminate; try reflexivity; [|exact (IHa H)].
  apply andb_true_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
Qed.

(** ** Vacuous generalization, for formulas without equality atoms *)
Lemma mneg_vac y a : lprov224 (Wim a (Wal y a)) -> lprov224 (Wim (Wn a) (Wal y (Wn a))).
Proof.
  intro H.
  pose proof (mcontra _ _ (MB6c y a)) as H1.
  pose proof (msyl _ _ _ H1 (mlpc_nn_elim _)) as H2.
  exact (msyl _ _ _ H2 (mal y _ _ (mcontra _ _ H))).
Qed.

Lemma mvac y a : occ y a = false -> noeq a = true -> lprov224 (Wim a (Wal y a)).
Proof.
  induction a as [u v|u v|a IHa b IHb|a IHa|z a IHa]; simpl; intros H Hn;
    try discriminate;
    try (apply orb_false_iff in H as [H0 H0']);
    try (apply andb_true_iff in Hn as [Hn1 Hn2]);
    repeat match goal with h : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in h end.
  - exact (MB6r u v y ltac:(assumption) ltac:(assumption)).
  - set (X := Wal y (Wim a b)).
    assert (H1 : lprov224 (Wim (Wn a) X)).
    { pose proof (mneg_vac y a (IHa ltac:(assumption) ltac:(assumption))) as N.
      refine (msyl _ _ _ N (mal y _ _ _)).
      exact (MDET _ _ (mlpc_C _ _ _) (MB3 a b)). }
    assert (H2 : lprov224 (Wim b X)).
    { exact (msyl _ _ _ (IHb ltac:(assumption) ltac:(assumption)) (mal y _ _ (mlpc_K b a))). }
    apply mder_lprov, mded. mmp (Wim (Wn X) X); [mdt (MB2 X)|]. apply mded.
    mmp (Wn a); [mdt H1|]. mmp (Wn b).
    + mmp (Wim a b); [mdt (mlpc_contra a b) | mdh].
    + mmp (Wn X); [mdt (mcontra _ _ H2) | mdh].
  - exact (mneg_vac y a (IHa H Hn)).
  - pose proof (mal z _ _ (IHa ltac:(assumption) ltac:(assumption))) as H1.
    exact (msyl _ _ _ H1 (MB6b z y a)).
Qed.

(** ** Leibniz substitution on quantifier-free membership matrices *)
Lemma meq_rv x y u :
  lprov224 (Wim (Weq x y) (Weq u (rv x y u))) /\ lprov224 (Wim (Weq x y) (Weq (rv x y u) u)).
Proof.
  unfold rv. destruct (Nat.eqb_spec u x) as [->|_].
  - split; [apply mlpc_id | apply meq_sym].
  - split; exact (MDET _ _ (mlpc_K _ _) (meq_refl u)).
Qed.

Lemma mleib x y a : qfm a = true ->
  lprov224 (Wim (Weq x y) (Wim a (ren x y a))) /\ lprov224 (Wim (Weq x y) (Wim (ren x y a) a)).
Proof.
  set (h := Weq x y).
  induction a as [u v|u v|a IHa b IHb|a IHa|z a IHa]; simpl; intros Hq; try discriminate.
  - destruct (meq_rv x y u) as [U1 U2]. destruct (meq_rv x y v) as [V1 V2].
    split; apply mder_lprov, mded.
    + mmp (Weq v (rv x y v)); [mmp (Weq u (rv x y u)); [mdt (meq_tr_el u (rv x y u) v (rv x y v))|]|].
      * mmp h; [mdt U1 | mdh].
      * mmp h; [mdt V1 | mdh].
    + mmp (Weq (rv x y v) v); [mmp (Weq (rv x y u) u); [mdt (meq_tr_el (rv x y u) u (rv x y v) v)|]|].
      * mmp h; [mdt U2 | mdh].
      * mmp h; [mdt V2 | mdh].
  - apply andb_true_iff in Hq as [Hqa Hqb].
    destruct (IHa Hqa) as [A1 A2]. destruct (IHb Hqb) as [B1' B2'].
    split; apply mder_lprov, mded, mded, mded.
    + mmp b; [mmp h; [mdt B1' | mdh] | mmp a; [mdh | mmp (ren x y a); [mmp h; [mdt A2 | mdh] | mdh]]].
    + mmp (ren x y b); [mmp h; [mdt B2' | mdh] | mmp (ren x y a); [mdh | mmp a; [mmp h; [mdt A1 | mdh] | mdh]]].
  - destruct (IHa Hq) as [A1 A2].
    split; apply mder_lprov, mded.
    + mmp (Wim (ren x y a) a); [mdt (mlpc_contra (ren x y a) a) | mmp h; [mdt A2 | mdh]].
    + mmp (Wim a (ren x y a)); [mdt (mlpc_contra a (ren x y a)) | mmp h; [mdt A1 | mdh]].
Qed.

Lemma noeq_ren x y a : noeq (ren x y a) = noeq a.
Proof. induction a; simpl; rewrite ?IHa, ?IHa1, ?IHa2; reflexivity. Qed.

(** ** Specialization and alphabetic variance on quantifier-free membership matrices *)
Lemma mall_ex x p q : lprov224 (Wim (Wal x (Wim p q)) (Wim (Wex x p) (Wex x q))).
Proof.
  unfold Wex.
  pose proof (MDET _ _ (MB4 x (Wim p q) (Wim (Wn q) (Wn p))) (MGEN x _ (mlpc_contra p q))) as H1.
  apply mder_lprov, mded.
  mmp (Wim (Wal x (Wn q)) (Wal x (Wn p))); [mdt (mlpc_contra (Wal x (Wn q)) (Wal x (Wn p)))|].
  mmp (Wal x (Wim (Wn q) (Wn p))); [mdt (MB4 x (Wn q) (Wn p))|].
  mmp (Wal x (Wim p q)); [mdt H1 | mdh].
Qed.

Lemma mspec x y a : x <> y -> qfm a = true -> lprov224 (Wim (Wal x a) (ren x y a)).
Proof.
  intros Hxy Hq. set (a' := ren x y a).
  destruct (mleib x y a Hq) as [L _].
  pose proof (MDET _ _ (mlpc_C _ _ _) L) as L'.
  pose proof (mal x _ _ L') as H1.
  pose proof (msyl _ _ _ H1 (mall_ex x (Weq x y) a')) as H2.
  pose proof (MDET _ _ (MDET _ _ (mlpc_C _ _ _) H2) (MB7 x y)) as H3.
  assert (Hn : noeq a' = true) by (unfold a'; rewrite noeq_ren; exact (qfm_noeq a Hq)).
  pose proof (mex x _ _ (mvac x a' (occ_ren_self x y a Hxy) Hn)) as H4.
  exact (msyl _ _ _ H3 (msyl _ _ _ H4 (MB6c x a'))).
Qed.

Lemma malpha x y a : x <> y -> qfm a = true -> occ y a = false ->
  lprov224 (Wim (Wal x a) (Wal y (ren x y a))).
Proof.
  intros Hxy Hq Hy.
  pose proof (mspec x y a Hxy Hq) as H1.
  refine (msyl _ _ _ (mvac y (Wal x a) _ _) (mal y _ _ H1)).
  - simpl. rewrite Hy, orb_false_r. apply Nat.eqb_neq. exact Hxy.
  - simpl. exact (qfm_noeq a Hq).
Qed.
