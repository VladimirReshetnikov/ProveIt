(** * L224E: equality as membership indiscernibility, and the interpretation of [lprov].

    [Eind x y] says that [x] and [y] have the same members and belong to the same sets, with the
    auxiliary bound name [aux x y = S (x + y)], distinct from both endpoints. [th] replaces every
    equality atom by [Eind] and keeps everything else. Every theorem of Jeff's pure-logic calculus
    [lprov], whose LB6a includes vacuity of equality for every fresh binder, interprets as a
    theorem of [lprov224], which has equality vacuity only at the 224's helper binder:

      [lprov_th : lprov a -> lprov224 (th a)].

    The equality axioms become facts about [Eind]: its vacuity follows from membership vacuity
    after renaming its auxiliary away; its existence row LB7 follows from the helper, which
    gives [x = y -> Eind x y] after transporting the helper's binder [wel x y]; Euclid and the
    two congruences follow by specialization through a common fresh name. *)
From Stdlib Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta.
From K230S Require Import KCode230.
From K224 Require Import L224Def L224Prop L224Meta.
Import ListNotations.

Definition Wiff (a b : wff) : wff := Wa (Wim a b) (Wim b a).
Definition Ein (v x y : nat) : wff := Wal v (Wiff (Wel v x) (Wel v y)).
Definition Eout (v x y : nat) : wff := Wal v (Wiff (Wel x v) (Wel y v)).
Definition Ev (v x y : nat) : wff := Wa (Ein v x y) (Eout v x y).
Definition aux (x y : nat) : nat := S (x + y).
Definition Eind (x y : nat) : wff := Ev (aux x y) x y.

Fixpoint th (a : wff) : wff :=
  match a with
  | Weq x y => Eind x y
  | Wel x y => Wel x y
  | Wim a b => Wim (th a) (th b)
  | Wn a => Wn (th a)
  | Wal x a => Wal x (th a)
  end.

Ltac neqb :=
  repeat match goal with
         | |- context [Nat.eqb ?a ?a] => rewrite (Nat.eqb_refl a)
         | |- context [Nat.eqb ?a ?b] => rewrite (proj2 (Nat.eqb_neq a b)) by lia
         end.

(** ** Syntax facts about the matrices *)
Lemma ren_in v v' x y : x <> v -> y <> v ->
  ren v v' (Wiff (Wel v x) (Wel v y)) = Wiff (Wel v' x) (Wel v' y).
Proof. intros. unfold Wiff, Wa. cbn [ren]. unfold rv. neqb. reflexivity. Qed.

Lemma ren_out v v' x y : x <> v -> y <> v ->
  ren v v' (Wiff (Wel x v) (Wel y v)) = Wiff (Wel x v') (Wel y v').
Proof. intros. unfold Wiff, Wa. cbn [ren]. unfold rv. neqb. reflexivity. Qed.

Lemma occ_in z v x y : z <> v -> z <> x -> z <> y -> occ z (Wiff (Wel v x) (Wel v y)) = false.
Proof. intros. unfold Wiff, Wa. cbn [occ]. neqb. reflexivity. Qed.

Lemma occ_out z v x y : z <> v -> z <> x -> z <> y -> occ z (Wiff (Wel x v) (Wel y v)) = false.
Proof. intros. unfold Wiff, Wa. cbn [occ]. neqb. reflexivity. Qed.

Lemma occ_Ev z v x y : z <> v -> z <> x -> z <> y -> occ z (Ev v x y) = false.
Proof. intros. unfold Ev, Ein, Eout, Wiff, Wa. cbn [occ]. neqb. reflexivity. Qed.

(** ** Propositional helpers *)
Lemma mand_mono a b a' b' :
  lprov224 (Wim a a') -> lprov224 (Wim b b') -> lprov224 (Wim (Wa a b) (Wa a' b')).
Proof.
  intros H1 H2. apply mder_lprov, mded. apply mder_andi.
  - mmp a; [mdt H1 | apply (mder_andl _ a b); mdh].
  - mmp b; [mdt H2 | apply (mder_andr _ a b); mdh].
Qed.

Lemma mal2 x p q r : lprov224 (Wim p (Wim q r)) ->
  lprov224 (Wim (Wal x p) (Wim (Wal x q) (Wal x r))).
Proof. intro H. exact (msyl _ _ _ (mal x _ _ H) (MB4 x q r)). Qed.

Lemma iff_euclid a b c : lprov224 (Wim (Wiff a b) (Wim (Wiff a c) (Wiff b c))).
Proof.
  apply mder_lprov, mded, mded. unfold Wiff. apply mder_andi.
  - apply mded. mmp a.
    + apply (mder_andl _ (Wim a c) (Wim c a)); mdh.
    + mmp b; [apply (mder_andr _ (Wim a b) (Wim b a)); mdh | mdh].
  - apply mded. mmp a.
    + apply (mder_andl _ (Wim a b) (Wim b a)); mdh.
    + mmp c; [apply (mder_andr _ (Wim a c) (Wim c a)); mdh | mdh].
Qed.

(** ** Renaming the auxiliary *)
Lemma Ev_alpha v v' x y : x <> v -> y <> v -> x <> v' -> y <> v' ->
  lprov224 (Wim (Ev v x y) (Ev v' x y)).
Proof.
  intros H1 H2 H3 H4. destruct (Nat.eq_dec v v') as [<-|Hvv]; [apply mlpc_id|].
  unfold Ev, Ein, Eout. apply mand_mono.
  - rewrite <- (ren_in v v' x y) by assumption.
    apply malpha; [exact Hvv | reflexivity | apply occ_in; lia].
  - rewrite <- (ren_out v v' x y) by assumption.
    apply malpha; [exact Hvv | reflexivity | apply occ_out; lia].
Qed.

Lemma Eind_to v x y : x <> v -> y <> v -> lprov224 (Wim (Eind x y) (Ev v x y)).
Proof. intros. apply Ev_alpha; unfold aux; lia. Qed.

Lemma Eind_of v x y : x <> v -> y <> v -> lprov224 (Wim (Ev v x y) (Eind x y)).
Proof. intros. apply Ev_alpha; unfold aux; lia. Qed.

(** ** The interpreted equality axioms *)
Lemma Eind_vac z x y : x <> z -> y <> z -> lprov224 (Wim (Eind x y) (Wal z (Eind x y))).
Proof.
  intros Hx Hy. set (v := S (x + y + z)).
  refine (msyl _ _ _ (Eind_to v x y _ _)
           (msyl _ _ _ (mvac z (Ev v x y) _ _) (mal z _ _ (Eind_of v x y _ _))));
    try (unfold v; lia).
  - apply occ_Ev; unfold v; lia.
  - reflexivity.
Qed.

Lemma meq_iff_in r x y : lprov224 (Wim (Weq x y) (Wiff (Wel r x) (Wel r y))).
Proof.
  apply mder_lprov, mded. unfold Wiff. apply mder_andi.
  - mmp (Weq x y); [mmp (Weq r r); [mdt (meq_tr_el r r x y) | mdt (meq_refl r)] | mdh].
  - mmp (Weq y x).
    + mmp (Weq r r); [mdt (meq_tr_el r r y x) | mdt (meq_refl r)].
    + mmp (Weq x y); [mdt (meq_sym x y) | mdh].
Qed.

Lemma meq_iff_out r x y : lprov224 (Wim (Weq x y) (Wiff (Wel x r) (Wel y r))).
Proof.
  apply mder_lprov, mded. unfold Wiff. apply mder_andi.
  - mmp (Weq r r); [mmp (Weq x y); [mdt (meq_tr_el x y r r) | mdh] | mdt (meq_refl r)].
  - mmp (Weq r r); [mmp (Weq y x); [mdt (meq_tr_el y x r r) | mmp (Weq x y); [mdt (meq_sym x y) | mdh]]
                   | mdt (meq_refl r)].
Qed.

Lemma meq_Ev r x y : lprov224 (Wim (Wal r (Weq x y)) (Ev r x y)).
Proof.
  unfold Ev, Ein, Eout. apply mder_lprov, mded. apply mder_andi.
  - mmp (Wal r (Weq x y)); [mdt (mal r _ _ (meq_iff_in r x y)) | mdh].
  - mmp (Wal r (Weq x y)); [mdt (mal r _ _ (meq_iff_out r x y)) | mdh].
Qed.

Lemma wel_apart x y : x <> wel x y /\ y <> wel x y.
Proof. unfold wel. pose proof (P_ge_l x y). pose proof (P_ge_r x y). lia. Qed.

(** The helper gives [x = y -> Eind x y]: generalize over its binder [wel x y], then rename. *)
Lemma Eq_Eind x y : lprov224 (Wim (Weq x y) (Eind x y)).
Proof.
  destruct (wel_apart x y) as [H1 H2].
  exact (msyl _ _ _ (MB6h x y) (msyl _ _ _ (meq_Ev (wel x y) x y) (Eind_of _ x y H1 H2))).
Qed.

Lemma Eind_ex x y : lprov224 (Wex x (Eind x y)).
Proof. exact (MDET _ _ (mex x _ _ (Eq_Eind x y)) (MB7 x y)). Qed.

Lemma Ev_euclid v x y z : lprov224 (Wim (Ev v x y) (Wim (Ev v x z) (Ev v y z))).
Proof.
  unfold Ev, Ein, Eout.
  pose proof (mal2 v _ _ _ (iff_euclid (Wel v x) (Wel v y) (Wel v z))) as Hin.
  pose proof (mal2 v _ _ _ (iff_euclid (Wel x v) (Wel y v) (Wel z v))) as Hout.
  apply mder_lprov, mded, mded. apply mder_andi.
  - mmp (Wal v (Wiff (Wel v x) (Wel v z))).
    + mmp (Wal v (Wiff (Wel v x) (Wel v y))); [mdt Hin|].
      apply (mder_andl _ _ (Wal v (Wiff (Wel x v) (Wel y v)))); mdh.
    + apply (mder_andl _ _ (Wal v (Wiff (Wel x v) (Wel z v)))); mdh.
  - mmp (Wal v (Wiff (Wel x v) (Wel z v))).
    + mmp (Wal v (Wiff (Wel x v) (Wel y v))); [mdt Hout|].
      apply (mder_andr _ (Wal v (Wiff (Wel v x) (Wel v y))) _); mdh.
    + apply (mder_andr _ (Wal v (Wiff (Wel v x) (Wel v z))) _); mdh.
Qed.

Lemma Eind_euclid x y z : lprov224 (Wim (Eind x y) (Wim (Eind x z) (Eind y z))).
Proof.
  set (v := S (x + y + z)).
  assert (A1 : lprov224 (Wim (Eind x y) (Ev v x y))) by (apply Eind_to; unfold v; lia).
  assert (A2 : lprov224 (Wim (Eind x z) (Ev v x z))) by (apply Eind_to; unfold v; lia).
  assert (A3 : lprov224 (Wim (Ev v y z) (Eind y z))) by (apply Eind_of; unfold v; lia).
  apply mder_lprov, mded, mded.
  mmp (Ev v y z); [mdt A3|].
  mmp (Ev v x z).
  - mmp (Ev v x y); [mdt (Ev_euclid v x y z) | mmp (Eind x y); [mdt A1 | mdh]].
  - mmp (Eind x z); [mdt A2 | mdh].
Qed.

Lemma Eind_el_l x y z : lprov224 (Wim (Eind x y) (Wim (Wel x z) (Wel y z))).
Proof.
  set (v := S (x + y + z)).
  assert (A1 : lprov224 (Wim (Eind x y) (Ev v x y))) by (apply Eind_to; unfold v; lia).
  assert (S1 : lprov224 (Wim (Eout v x y) (Wiff (Wel x z) (Wel y z)))).
  { unfold Eout. rewrite <- (ren_out v z x y) by (unfold v; lia).
    apply mspec; [unfold v; lia | reflexivity]. }
  apply mder_lprov, mded, mded.
  mmp (Wel x z); [|mdh].
  apply (mder_andl _ _ (Wim (Wel y z) (Wel x z))).
  mmp (Eout v x y); [mdt S1|].
  apply (mder_andr _ (Ein v x y) _). mmp (Eind x y); [mdt A1 | mdh].
Qed.

Lemma Eind_el_r x y z : lprov224 (Wim (Eind x y) (Wim (Wel z x) (Wel z y))).
Proof.
  set (v := S (x + y + z)).
  assert (A1 : lprov224 (Wim (Eind x y) (Ev v x y))) by (apply Eind_to; unfold v; lia).
  assert (S1 : lprov224 (Wim (Ein v x y) (Wiff (Wel z x) (Wel z y)))).
  { unfold Ein. rewrite <- (ren_in v z x y) by (unfold v; lia).
    apply mspec; [unfold v; lia | reflexivity]. }
  apply mder_lprov, mded, mded.
  mmp (Wel z x); [|mdh].
  apply (mder_andl _ _ (Wim (Wel z y) (Wel z x))).
  mmp (Ein v x y); [mdt S1|].
  apply (mder_andl _ _ (Eout v x y)). mmp (Eind x y); [mdt A1 | mdh].
Qed.

(** ** The interpretation *)
Theorem lprov_th a : lprov a -> lprov224 (th a).
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz
                  | x y a | x a | x y | x y z | x y z | x y z].
  - exact (MDET _ _ IH1 IH2).
  - exact (MGEN _ _ IH).
  - apply MB1.
  - apply MB2.
  - apply MB3.
  - apply MB4.
  - change (lprov224 (Wa (Wim (Eind x y) (Wal z (Eind x y))) (Wim (Wel x y) (Wal z (Wel x y))))).
    apply mder_lprov, mder_andi; apply mthm; [apply Eind_vac | apply MB6r]; assumption.
  - apply MB6b.
  - exact (MB6c x (th a)).
  - exact (Eind_ex x y).
  - exact (Eind_euclid x y z).
  - exact (Eind_el_l x y z).
  - exact (Eind_el_r x y z).
Qed.

Print Assumptions lprov_th.
