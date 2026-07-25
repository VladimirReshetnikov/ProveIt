(* ===================================================================== *)
(*  Relativization.v                                                      *)
(*                                                                       *)
(*  Generic relativization of first-order formulas to the loop-free      *)
(*  elements of a binary-relation structure.  A quantified variable is   *)
(*  guarded by [x \notin x]; the resulting formula is interpreted in the *)
(*  subtype carrying precisely that guard.                                *)
(* ===================================================================== *)

From Stdlib Require Import Lia Logic.ProofIrrelevance.
Require Import FirstOrder.Fol.

(* The formula saying that variable [i] has no self-loop. *)
Definition loopFreeAt (i : nat) : form :=
  fImp (fMem i i) fBot.

(* Restrict each quantifier to loop-free elements. *)
Fixpoint relativize (f : form) : form :=
  match f with
  | fMem i j => fMem i j
  | fEq i j => fEq i j
  | fBot => fBot
  | fImp a b => fImp (relativize a) (relativize b)
  | fAnd a b => fAnd (relativize a) (relativize b)
  | fOr a b => fOr (relativize a) (relativize b)
  | fAll a => fAll (fImp (loopFreeAt 0) (relativize a))
  | fEx a => fEx (fAnd (loopFreeAt 0) (relativize a))
  end.

Lemma relativize_rename : forall f r,
  relativize (rename r f) = rename r (relativize f).
Proof.
  induction f as
      [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb
      | a IHa | a IHa]; intro r; cbn [rename relativize loopFreeAt up].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma Free_loopFreeAt : forall n i,
  Free n (loopFreeAt i) <-> n = i.
Proof.
  intros n i. unfold loopFreeAt. cbn [Free]. tauto.
Qed.

(* Relativization introduces guards only for variables bound at the same
   quantifier, so it preserves exactly the externally free variables. *)
Lemma Free_relativize : forall n f,
  Free n (relativize f) <-> Free n f.
Proof.
  intros n f. revert n. induction f as
      [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb
      | a IHa | a IHa]; intro n; cbn [relativize Free loopFreeAt].
  - tauto.
  - tauto.
  - tauto.
  - rewrite IHa, IHb. tauto.
  - rewrite IHa, IHb. tauto.
  - rewrite IHa, IHb. tauto.
  - rewrite IHa. assert (S n <> 0) by discriminate. tauto.
  - rewrite IHa. assert (S n <> 0) by discriminate. tauto.
Qed.

Lemma Free_relativize_iff : forall f n,
  Free n (relativize f) <-> Free n f.
Proof.
  intros f n. apply Free_relativize.
Qed.

Lemma Free_relativize_forward : forall f n,
  Free n (relativize f) -> Free n f.
Proof.
  intros f n H. apply (proj1 (Free_relativize n f)). exact H.
Qed.

Lemma Free_relativize_rev : forall f n,
  Free n f -> Free n (relativize f).
Proof.
  intros f n H. apply (proj2 (Free_relativize n f)). exact H.
Qed.

Lemma Sentence_relativize_iff : forall f,
  Sentence (relativize f) <-> Sentence f.
Proof.
  intro f. unfold Sentence. split; intros H n Hfree.
  - apply (H n). apply Free_relativize_rev. exact Hfree.
  - apply (H n). apply Free_relativize_forward. exact Hfree.
Qed.

Lemma Sentence_relativize : forall f,
  Sentence f -> Sentence (relativize f).
Proof.
  intros f H. apply (proj2 (Sentence_relativize_iff f)). exact H.
Qed.

(* The induced structure on the loop-free elements. *)
Definition RelDomain {V : Type} (mem : V -> V -> Prop) : Type :=
  { x : V | ~ mem x x }.

Definition relDomainMem {V : Type} (mem : V -> V -> Prop) :
    RelDomain mem -> RelDomain mem -> Prop :=
  fun x y => mem (proj1_sig x) (proj1_sig y).

Lemma Sat_loopFreeAt :
  forall (V : Type) (mem : V -> V -> Prop) (e : nat -> V) i,
    Sat V mem e (loopFreeAt i) <-> ~ mem (e i) (e i).
Proof.
  intros V mem e i. unfold loopFreeAt. cbn [Sat]. tauto.
Qed.

Lemma RelDomain_eq {V : Type} {mem : V -> V -> Prop}
    (x y : RelDomain mem) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x hx], y as [y hy]. cbn. intro H. subst y.
  f_equal. apply proof_irrelevance.
Qed.

Lemma relDomain_scons_value {V : Type} {mem : V -> V -> Prop}
    (d : RelDomain mem) (e : nat -> RelDomain mem) :
  forall n,
    proj1_sig (scons (RelDomain mem) d e n) =
    scons V (proj1_sig d) (fun k => proj1_sig (e k)) n.
Proof.
  intro n. destruct n; reflexivity.
Qed.

(* Satisfaction transport along that pointwise equality, in the form used
   by both quantifier cases of [Sat_relativize]. *)
Lemma Sat_relativize_scons {V : Type} {mem : V -> V -> Prop}
    (a : form) (d : RelDomain mem) (e : nat -> RelDomain mem) :
  Sat V mem (fun n => proj1_sig (scons (RelDomain mem) d e n)) a <->
  Sat V mem (scons V (proj1_sig d) (fun n => proj1_sig (e n))) a.
Proof.
  apply Sat_ext. apply relDomain_scons_value.
Qed.

(* Relativizing a formula in the ambient structure is exactly the same as
   evaluating the original formula in the induced loop-free substructure. *)
Theorem Sat_relativize :
  forall (V : Type) (mem : V -> V -> Prop) (f : form)
         (e : nat -> RelDomain mem),
    Sat V mem (fun n => proj1_sig (e n)) (relativize f) <->
    Sat (RelDomain mem) (relDomainMem mem) e f.
Proof.
  intros V mem f.
  induction f as
      [i j | i j | | a IHa b IHb | a IHa b IHb | a IHa b IHb
      | a IHa | a IHa]; intro e; cbn [relativize Sat loopFreeAt relDomainMem].
  - tauto.
  - split.
    + apply RelDomain_eq.
    + intro H. now f_equal.
  - tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - specialize (IHa e). specialize (IHb e). tauto.
  - split.
    + intros H d.
      apply (proj1 (IHa (scons (RelDomain mem) d e))).
      apply (proj2 (Sat_relativize_scons (relativize a) d e)).
      apply H. exact (proj2_sig d).
    + intros H d hd.
      pose (d' := (exist _ d hd : RelDomain mem)).
      apply (proj1 (Sat_relativize_scons (relativize a) d' e)).
      apply (proj2 (IHa (scons (RelDomain mem) d' e))).
      exact (H d').
  - split.
    + intros [d [hd H]].
      pose (d' := (exist _ d hd : RelDomain mem)).
      exists d'.
      apply (proj1 (IHa (scons (RelDomain mem) d' e))).
      apply (proj2 (Sat_relativize_scons (relativize a) d' e)).
      exact H.
    + intros [d H].
      exists (proj1_sig d). split.
      * exact (proj2_sig d).
      * apply (proj1 (Sat_relativize_scons (relativize a) d e)).
        apply (proj2 (IHa (scons (RelDomain mem) d e))). exact H.
Qed.
