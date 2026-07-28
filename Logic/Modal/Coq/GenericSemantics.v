(**
  Generic Tarski semantics for propositional connectives.

  This file ports the first twenty active declarations at lines 25--121 of
  the pinned Foundation module [Logic/Semantics.lean].  The development is
  independent of modal syntax: [generic_connectives] supplies an arbitrary
  formula type's six propositional operations, while [generic_semantics]
  contains only an arbitrary satisfaction predicate.  The six clause records
  and their aggregate are the direct Coq counterparts of Foundation's
  per-connective semantics classes and [Semantics.Tarski].

  Foundation has both lists and duplicate-free [Finset] values.  The latter
  are represented here by lists, consistently with the rest of the modal
  port.  Their readback statements use only [In], so order and duplicate
  multiplicity are semantically irrelevant.  The two singleton-normalized
  folds are exposed as infrastructure helpers; the numbered declarations
  remain an exact 1--20 source mapping.

  Every result in this tranche is constructive.
*)

From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Infrastructure corresponding to Foundation's separately imported
    [LogicalConnective].  It is not one of this file's twenty source
    declarations. *)
Record generic_connectives (F : Type) : Type := {
  generic_top : F;
  generic_bottom : F;
  generic_and : F -> F -> F;
  generic_or : F -> F -> F;
  generic_imp : F -> F -> F;
  generic_neg : F -> F
}.

Arguments generic_top {F} _.
Arguments generic_bottom {F} _.
Arguments generic_and {F} _ _ _.
Arguments generic_or {F} _ _ _.
Arguments generic_imp {F} _ _ _.
Arguments generic_neg {F} _ _.

(** Source declaration 1/20: [LO.Semantics].  As in Foundation, this record
    contains only the satisfaction relation; propositional syntax is supplied
    independently by [generic_connectives]. *)
Record generic_semantics (M F : Type) : Type := {
  generic_models : M -> F -> Prop
}.

Arguments generic_models {M F} _ _ _.

(** Source declaration 2/20: [Semantics.NotModels]. *)
Definition generic_not_models {M F : Type}
    (S : generic_semantics M F) (m : M) (p : F) : Prop :=
  ~ generic_models S m p.

(** Source declaration 3/20: [Semantics.Top]. *)
Record generic_semantics_top {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_top :
    forall m : M, generic_models S m (generic_top C)
}.

(** Source declaration 4/20: [Semantics.Bot]. *)
Record generic_semantics_bottom {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_bottom :
    forall m : M, ~ generic_models S m (generic_bottom C)
}.

(** Source declaration 5/20: [Semantics.And]. *)
Record generic_semantics_and {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_and :
    forall (m : M) (p q : F),
      generic_models S m (generic_and C p q) <->
      generic_models S m p /\ generic_models S m q
}.

(** Source declaration 6/20: [Semantics.Or]. *)
Record generic_semantics_or {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_or :
    forall (m : M) (p q : F),
      generic_models S m (generic_or C p q) <->
      generic_models S m p \/ generic_models S m q
}.

(** Source declaration 7/20: [Semantics.Imp]. *)
Record generic_semantics_imp {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_imp :
    forall (m : M) (p q : F),
      generic_models S m (generic_imp C p q) <->
      (generic_models S m p -> generic_models S m q)
}.

(** Source declaration 8/20: [Semantics.Not]. *)
Record generic_semantics_neg {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_neg :
    forall (m : M) (p : F),
      generic_models S m (generic_neg C p) <->
      ~ generic_models S m p
}.

(** Source declaration 9/20: [Semantics.Tarski]. *)
Record generic_tarski {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_tarski_top : generic_semantics_top C S;
  generic_tarski_bottom : generic_semantics_bottom C S;
  generic_tarski_and : generic_semantics_and C S;
  generic_tarski_or : generic_semantics_or C S;
  generic_tarski_imp : generic_semantics_imp C S;
  generic_tarski_neg : generic_semantics_neg C S
}.

(** Source declaration 10/20: [Semantics.models_iff].  Biconditional is
    represented exactly as the source definition: the conjunction of the
    two directed implications. *)
Lemma generic_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (p q : F),
    generic_models S m
      (generic_and C (generic_imp C p q) (generic_imp C q p)) <->
    (generic_models S m p <-> generic_models S m q).
Proof.
  intros M F C S HT m p q.
  destruct HT as [_ _ [HAnd] _ [HImp] _].
  rewrite HAnd, !HImp.
  split.
  - intros [Hpq Hqp]; split; assumption.
  - intros [Hpq Hqp]; split; assumption.
Qed.

(** Source declaration 11/20: [Semantics.models_list_conj]. *)
Lemma generic_models_list_conj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list F),
    generic_models S m
      (fold_right (generic_and C) (generic_top C) l) <->
    forall p, In p l -> generic_models S m p.
Proof.
  intros M F C S HT m l.
  destruct HT as [[HTop] _ [HAnd] _ _ _].
  induction l as [|p l IH]; simpl.
  - split.
    + intros _ q Hq. contradiction.
    + intros _. apply HTop.
  - rewrite HAnd. split.
    + intros [Hp Hl] q [<- | Hq]; [exact Hp |].
      now apply (proj1 IH).
    + intro Hall; split.
      * apply Hall. now left.
      * apply (proj2 IH). intros q Hq.
        apply Hall. now right.
Qed.

(** Infrastructure helper for source [List.conj2].  Unlike the ordinary
    fold, a singleton is returned literally rather than conjoined with top. *)
Fixpoint generic_list_conj2 {F : Type}
    (C : generic_connectives F) (l : list F) : F :=
  match l with
  | [] => generic_top C
  | p :: rest =>
      match rest with
      | [] => p
      | _ => generic_and C p (generic_list_conj2 C rest)
      end
  end.

(** Source declaration 12/20: [Semantics.models_list_conj2]. *)
Lemma generic_models_list_conj2 :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list F),
    generic_models S m (generic_list_conj2 C l) <->
    forall p, In p l -> generic_models S m p.
Proof.
  intros M F C S HT m l.
  destruct HT as [[HTop] _ [HAnd] _ _ _].
  induction l as [|p rest IH].
  - simpl. split.
    + intros _ q Hq. contradiction.
    + intros _. apply HTop.
  - destruct rest as [|q rest].
    + simpl. split.
      * intros Hp r [<- | Hr]; [exact Hp | contradiction].
      * intro Hall. apply Hall. now left.
    + simpl generic_list_conj2.
      rewrite HAnd, IH. split.
      * intros [Hp Hrest] r [<- | Hr]; [exact Hp |].
        now apply Hrest.
      * intro Hall; split.
        -- apply Hall. now left.
        -- intros r Hr. apply Hall. now right.
Qed.

(** Source declaration 13/20: [Semantics.models_list_conj']. *)
Lemma generic_models_list_conj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list I) (f : I -> F),
    generic_models S m (generic_list_conj2 C (map f l)) <->
    forall i, In i l -> generic_models S m (f i).
Proof.
  intros M F I C S HT m l f.
  rewrite (generic_models_list_conj2 HT m (map f l)).
  split.
  - intros Hall i Hi. apply Hall with (p := f i).
    now apply in_map.
  - intros Hall p Hp.
    apply in_map_iff in Hp.
    destruct Hp as [i [Hfi Hi]].
    rewrite <- Hfi. now apply Hall.
Qed.

(** Source declaration 14/20: [Semantics.models_finset_conj].  The list is
    an extensional finite-set representative; the readback ignores order and
    duplicates. *)
Lemma generic_models_finset_conj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (s : list F),
    generic_models S m (generic_list_conj2 C s) <->
    forall p, In p s -> generic_models S m p.
Proof. exact generic_models_list_conj2. Qed.

(** Source declaration 15/20: [Semantics.models_finset_conj']. *)
Lemma generic_models_finset_conj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (s : list I) (f : I -> F),
    generic_models S m (generic_list_conj2 C (map f s)) <->
    forall i, In i s -> generic_models S m (f i).
Proof. exact generic_models_list_conj_map. Qed.

(** Source declaration 16/20: [Semantics.models_list_disj]. *)
Lemma generic_models_list_disj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list F),
    generic_models S m
      (fold_right (generic_or C) (generic_bottom C) l) <->
    exists p, In p l /\ generic_models S m p.
Proof.
  intros M F C S HT m l.
  destruct HT as [_ [HBottom] _ [HOr] _ _].
  induction l as [|p l IH]; simpl.
  - split.
    + intro H. exfalso. exact (HBottom m H).
    + intros [q [Hq _]]. contradiction.
  - rewrite HOr. split.
    + intros [Hp | Hl].
      * exists p. split; [now left | exact Hp].
      * destruct (proj1 IH Hl) as [q [HqIn Hq]].
        exists q. split; [now right | exact Hq].
    + intros [q [[<- | HqIn] Hq]].
      * now left.
      * right. apply (proj2 IH). now exists q.
Qed.

(** Infrastructure helper for source [List.disj2].  A singleton is returned
    literally rather than disjoined with bottom. *)
Fixpoint generic_list_disj2 {F : Type}
    (C : generic_connectives F) (l : list F) : F :=
  match l with
  | [] => generic_bottom C
  | p :: rest =>
      match rest with
      | [] => p
      | _ => generic_or C p (generic_list_disj2 C rest)
      end
  end.

(** Source declaration 17/20: [Semantics.models_list_disj2]. *)
Lemma generic_models_list_disj2 :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list F),
    generic_models S m (generic_list_disj2 C l) <->
    exists p, In p l /\ generic_models S m p.
Proof.
  intros M F C S HT m l.
  destruct HT as [_ [HBottom] _ [HOr] _ _].
  induction l as [|p rest IH].
  - simpl. split.
    + intro H. exfalso. exact (HBottom m H).
    + intros [q [Hq _]]. contradiction.
  - destruct rest as [|q rest].
    + simpl. split.
      * intro Hp. exists p. split; [now left | exact Hp].
      * intros [r [[<- | Hr] HrModels]];
          [exact HrModels | contradiction].
    + simpl generic_list_disj2.
      rewrite HOr, IH. split.
      * intros [Hp | [r [HrIn Hr]]].
        -- exists p. split; [now left | exact Hp].
        -- exists r. split; [now right | exact Hr].
      * intros [r [[<- | HrIn] Hr]].
        -- now left.
        -- right. now exists r.
Qed.

(** Source declaration 18/20: [Semantics.models_list_disj']. *)
Lemma generic_models_list_disj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (l : list I) (f : I -> F),
    generic_models S m (generic_list_disj2 C (map f l)) <->
    exists i, In i l /\ generic_models S m (f i).
Proof.
  intros M F I C S HT m l f.
  rewrite (generic_models_list_disj2 HT m (map f l)).
  split.
  - intros [p [HpIn Hp]].
    apply in_map_iff in HpIn.
    destruct HpIn as [i [Hfi Hi]].
    exists i. split; [exact Hi |].
    rewrite Hfi. exact Hp.
  - intros [i [Hi HiModels]].
    exists (f i). split.
    + now apply in_map.
    + exact HiModels.
Qed.

(** Source declaration 19/20: [Semantics.models_finset_disj].  As above,
    list membership gives the duplicate-insensitive finite-set reading. *)
Lemma generic_models_finset_disj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (s : list F),
    generic_models S m (generic_list_disj2 C s) <->
    exists p, In p s /\ generic_models S m p.
Proof. exact generic_models_list_disj2. Qed.

(** Source declaration 20/20: [Semantics.models_finset_disj']. *)
Lemma generic_models_finset_disj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_tarski C S -> forall (m : M) (s : list I) (f : I -> F),
    generic_models S m (generic_list_disj2 C (map f s)) <->
    exists i, In i s /\ generic_models S m (f i).
Proof. exact generic_models_list_disj_map. Qed.
