(**
  Generic Tarski semantics for propositional connectives.

  This file ports all sixty-seven active declarations at lines 25--353 of
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
  remain an exact 1--67 source mapping.

  The Tarski and model-set core is constructive.  [Classical_Prop] is used
  only where the source extracts a counterexample from a negated universal or
  eliminates double negation of an arbitrary satisfaction proposition.  In
  the final compactness section, extracting a finite unsatisfiable witness and
  compact consequence are classical; cumulative finite support and compactness
  of a cumulative union remain constructive.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop Arith.PeanoNat.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Infrastructure corresponding to Foundation's separately imported
    [LogicalConnective].  It is not one of the numbered source declarations. *)
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

(** Source declaration 1/67: [LO.Semantics].  As in Foundation, this record
    contains only the satisfaction relation; propositional syntax is supplied
    independently by [generic_connectives]. *)
Record generic_semantics (M F : Type) : Type := {
  generic_models : M -> F -> Prop
}.

Arguments generic_models {M F} _ _ _.

(** Source declaration 2/67: [Semantics.NotModels]. *)
Definition generic_not_models {M F : Type}
    (S : generic_semantics M F) (m : M) (p : F) : Prop :=
  ~ generic_models S m p.

(** Source declaration 3/67: [Semantics.Top]. *)
Record generic_semantics_top {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_top :
    forall m : M, generic_models S m (generic_top C)
}.

(** Source declaration 4/67: [Semantics.Bot]. *)
Record generic_semantics_bottom {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_bottom :
    forall m : M, ~ generic_models S m (generic_bottom C)
}.

(** Source declaration 5/67: [Semantics.And]. *)
Record generic_semantics_and {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_and :
    forall (m : M) (p q : F),
      generic_models S m (generic_and C p q) <->
      generic_models S m p /\ generic_models S m q
}.

(** Source declaration 6/67: [Semantics.Or]. *)
Record generic_semantics_or {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_or :
    forall (m : M) (p q : F),
      generic_models S m (generic_or C p q) <->
      generic_models S m p \/ generic_models S m q
}.

(** Source declaration 7/67: [Semantics.Imp]. *)
Record generic_semantics_imp {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_imp :
    forall (m : M) (p q : F),
      generic_models S m (generic_imp C p q) <->
      (generic_models S m p -> generic_models S m q)
}.

(** Source declaration 8/67: [Semantics.Not]. *)
Record generic_semantics_neg {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_models_neg :
    forall (m : M) (p : F),
      generic_models S m (generic_neg C p) <->
      ~ generic_models S m p
}.

(** Source declaration 9/67: [Semantics.Tarski]. *)
Record generic_tarski {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F) : Prop := {
  generic_tarski_top : generic_semantics_top C S;
  generic_tarski_bottom : generic_semantics_bottom C S;
  generic_tarski_and : generic_semantics_and C S;
  generic_tarski_or : generic_semantics_or C S;
  generic_tarski_imp : generic_semantics_imp C S;
  generic_tarski_neg : generic_semantics_neg C S
}.

(** Source declaration 10/67: [Semantics.models_iff].  Biconditional is
    represented exactly as the source definition: the conjunction of the
    two directed implications.  Requiring only the conjunction and
    implication clauses strengthens the source's aggregate-Tarski boundary. *)
Lemma generic_models_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_and C S ->
    generic_semantics_imp C S ->
    forall (m : M) (p q : F),
    generic_models S m
      (generic_and C (generic_imp C p q) (generic_imp C q p)) <->
    (generic_models S m p <-> generic_models S m q).
Proof.
  intros M F C S [HAnd] [HImp] m p q.
  rewrite HAnd, !HImp.
  split.
  - intros [Hpq Hqp]; split; assumption.
  - intros [Hpq Hqp]; split; assumption.
Qed.

(** Source declaration 11/67: [Semantics.models_list_conj].  Only the top
    and conjunction clauses are used, strengthening the source hypothesis. *)
Lemma generic_models_list_conj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (l : list F),
    generic_models S m
      (fold_right (generic_and C) (generic_top C) l) <->
    forall p, In p l -> generic_models S m p.
Proof.
  intros M F C S [HTop] [HAnd] m l.
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

(** Source declaration 12/67: [Semantics.models_list_conj2].  It retains the
    minimal top-and-conjunction boundary of declaration 11. *)
Lemma generic_models_list_conj2 :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (l : list F),
    generic_models S m (generic_list_conj2 C l) <->
    forall p, In p l -> generic_models S m p.
Proof.
  intros M F C S [HTop] [HAnd] m l.
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

(** Source declaration 13/67: [Semantics.models_list_conj'].  It retains the
    minimal top-and-conjunction boundary of declaration 11. *)
Lemma generic_models_list_conj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (l : list I) (f : I -> F),
    generic_models S m (generic_list_conj2 C (map f l)) <->
    forall i, In i l -> generic_models S m (f i).
Proof.
  intros M F I C S Htop Hand m l f.
  rewrite (generic_models_list_conj2 Htop Hand m (map f l)).
  split.
  - intros Hall i Hi. apply Hall with (p := f i).
    now apply in_map.
  - intros Hall p Hp.
    apply in_map_iff in Hp.
    destruct Hp as [i [Hfi Hi]].
    rewrite <- Hfi. now apply Hall.
Qed.

(** Source declaration 14/67: [Semantics.models_finset_conj].  The list is
    an extensional finite-set representative; the readback ignores order and
    duplicates.  Only the top and conjunction clauses are required. *)
Lemma generic_models_finset_conj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (s : list F),
    generic_models S m (generic_list_conj2 C s) <->
    forall p, In p s -> generic_models S m p.
Proof. exact generic_models_list_conj2. Qed.

(** Source declaration 15/67: [Semantics.models_finset_conj'].  Only the top
    and conjunction clauses are required. *)
Lemma generic_models_finset_conj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall (m : M) (s : list I) (f : I -> F),
    generic_models S m (generic_list_conj2 C (map f s)) <->
    forall i, In i s -> generic_models S m (f i).
Proof. exact generic_models_list_conj_map. Qed.

(** Source declaration 16/67: [Semantics.models_list_disj].  Only the bottom
    and disjunction clauses are used, strengthening the source hypothesis. *)
Lemma generic_models_list_disj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (l : list F),
    generic_models S m
      (fold_right (generic_or C) (generic_bottom C) l) <->
    exists p, In p l /\ generic_models S m p.
Proof.
  intros M F C S [HBottom] [HOr] m l.
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

(** Source declaration 17/67: [Semantics.models_list_disj2].  It retains the
    minimal bottom-and-disjunction boundary of declaration 16. *)
Lemma generic_models_list_disj2 :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (l : list F),
    generic_models S m (generic_list_disj2 C l) <->
    exists p, In p l /\ generic_models S m p.
Proof.
  intros M F C S [HBottom] [HOr] m l.
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

(** Source declaration 18/67: [Semantics.models_list_disj'].  It retains the
    minimal bottom-and-disjunction boundary of declaration 16. *)
Lemma generic_models_list_disj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (l : list I) (f : I -> F),
    generic_models S m (generic_list_disj2 C (map f l)) <->
    exists i, In i l /\ generic_models S m (f i).
Proof.
  intros M F I C S Hbottom Hor m l f.
  rewrite (generic_models_list_disj2 Hbottom Hor m (map f l)).
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

(** Source declaration 19/67: [Semantics.models_finset_disj].  As above,
    list membership gives the duplicate-insensitive finite-set reading, and
    only the bottom and disjunction clauses are required. *)
Lemma generic_models_finset_disj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (s : list F),
    generic_models S m (generic_list_disj2 C s) <->
    exists p, In p s /\ generic_models S m p.
Proof. exact generic_models_list_disj2. Qed.

(** Source declaration 20/67: [Semantics.models_finset_disj'].  Only the
    bottom and disjunction clauses are required. *)
Lemma generic_models_finset_disj_map :
  forall (M F I : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    forall (m : M) (s : list I) (f : I -> F),
    generic_models S m (generic_list_disj2 C (map f s)) <->
    exists i, In i s /\ generic_models S m (f i).
Proof. exact generic_models_list_disj_map. Qed.

(** * Model sets, validity, and satisfiability *)

(** Source declaration 21/67: [Semantics.ModelsSet].  Source sets are
    represented extensionally as predicates. *)
Record generic_models_set {M F : Type}
    (S : generic_semantics M F) (m : M) (T : F -> Prop) : Prop := {
  generic_models_set_elim :
    forall p : F, T p -> generic_models S m p
}.

(** Source declaration 22/67: [Semantics.Valid]. *)
Definition generic_valid {M F : Type}
    (S : generic_semantics M F) (p : F) : Prop :=
  forall m : M, generic_models S m p.

(** Source declaration 23/67: [Semantics.Satisfiable]. *)
Definition generic_satisfiable {M F : Type}
    (S : generic_semantics M F) (T : F -> Prop) : Prop :=
  exists m : M, generic_models_set S m T.

(** Source declaration 24/67: [Semantics.models]. *)
Definition generic_model_set {M F : Type}
    (S : generic_semantics M F) (T : F -> Prop) : M -> Prop :=
  fun m => generic_models_set S m T.

(** Source declaration 25/67: [Semantics.theory]. *)
Definition generic_theory {M F : Type}
    (S : generic_semantics M F) (m : M) : F -> Prop :=
  fun p => generic_models S m p.

(** Source declaration 26/67: [Semantics.Meaningful]. *)
Record generic_meaningful {M F : Type}
    (S : generic_semantics M F) (m : M) : Prop := {
  generic_exists_not_models :
    exists p : F, generic_not_models S m p
}.

(** Source declaration 27/67: the [Meaningful] instance supplied by a
    falsity clause. *)
Definition generic_meaningful_of_bottom {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F)
    (Hbottom : generic_semantics_bottom C S) (m : M) :
    generic_meaningful S m.
Proof.
  destruct Hbottom as [Hbottom]. constructor.
  exists (generic_bottom C). exact (Hbottom m).
Defined.

(** Source declaration 28/67: [Semantics.meaningful_iff]. *)
Lemma generic_meaningful_iff :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    generic_meaningful S m <->
    exists p : F, generic_not_models S m p.
Proof.
  intros M F S m; split.
  - intros [H]. exact H.
  - intro H. now constructor.
Qed.

(** Source declaration 29/67: [Semantics.not_meaningful_iff].  This is the
    first genuinely classical declaration: its forward direction eliminates
    double negation of an arbitrary satisfaction proposition. *)
Lemma generic_not_meaningful_iff :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    ~ generic_meaningful S m <->
    forall p : F, generic_models S m p.
Proof.
  intros M F S m; split.
  - intros Hnot p. apply NNPP. intro Hnotp.
    apply Hnot. constructor. now exists p.
  - intros Hall [Hcounter].
    destruct Hcounter as [p Hnotp]. exact (Hnotp (Hall p)).
Qed.

(** Source declaration 30/67: [Semantics.modelsSet_iff]. *)
Lemma generic_models_set_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (m : M) (T : F -> Prop),
    generic_models_set S m T <->
    forall p : F, T p -> generic_models S m p.
Proof.
  intros M F S m T; split.
  - intros [H]. exact H.
  - intro H. now constructor.
Qed.

(** Source declaration 31/67: [Semantics.modelsTheory_theory]. *)
Lemma generic_models_theory :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    generic_models_set S m (generic_theory S m).
Proof.
  intros M F S m. constructor. intros p Hp. exact Hp.
Qed.

(** Source declaration 32/67: [Semantics.theory_satisfiable]. *)
Lemma generic_theory_satisfiable :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    generic_satisfiable S (generic_theory S m).
Proof.
  intros M F S m. exists m. apply generic_models_theory.
Qed.

(** Unnumbered infrastructure: classical finite De Morgan.  Keeping this
    independent of formulas and semantics lets later finite satisfiability
    arguments reuse the only counterexample-extraction step. *)
Lemma finite_not_forall_iff_exists_not :
  forall (A : Type) (P : A -> Prop) (l : list A),
    ~ (forall x : A, In x l -> P x) <->
    exists x : A, In x l /\ ~ P x.
Proof.
  intros A P l; split.
  - intro Hnotall. apply NNPP. intro Hnone.
    apply Hnotall. intros x Hx. apply NNPP. intro Hnotx.
    apply Hnone. now exists x.
  - intros [x [Hx Hnotx]] Hall. exact (Hnotx (Hall x Hx)).
Qed.

(** Source declaration 33/67: [Semantics.not_satisfiable_finset].  Lists
    replace Finset and [map] replaces duplicate-removing image; declaration
    18/20 makes the result duplicate-insensitive.  The source's
    [DecidableEq] is therefore unnecessary.  Finite counterexample extraction
    is classical because satisfaction propositions need not be decidable.
    Only bottom, disjunction, and negation clauses are required. *)
Lemma generic_not_satisfiable_finset :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_bottom C S ->
    generic_semantics_or C S ->
    generic_semantics_neg C S ->
    forall t : list F,
    ~ generic_satisfiable S (fun p => In p t) <->
    generic_valid S (generic_list_disj2 C (map (generic_neg C) t)).
Proof.
  intros M F C S Hbottom Hor Hneg t.
  split.
  - intros Hunsat m.
    apply (proj2 (generic_models_finset_disj_map
      Hbottom Hor m t (generic_neg C))).
    assert (Hnotall :
      ~ (forall p : F, In p t -> generic_models S m p)).
    { intro Hall. apply Hunsat. exists m. now constructor. }
    destruct (proj1 (finite_not_forall_iff_exists_not
      (fun p : F => generic_models S m p) t) Hnotall)
      as [p [HpIn Hnotp]].
    exists p. split; [exact HpIn |].
    apply (proj2 (generic_models_neg
      Hneg m p)). exact Hnotp.
  - intros Hvalid [m Hmodels].
    pose proof (proj1 (generic_models_finset_disj_map
      Hbottom Hor m t (generic_neg C)) (Hvalid m)) as Hcounter.
    destruct Hcounter as [p [HpIn Hnegp]].
    apply (proj1 (generic_models_neg
      Hneg m p) Hnegp).
    exact (generic_models_set_elim Hmodels HpIn).
Qed.

(** Source declaration 34/67: [Semantics.satisfiable_conj2].  Only top and
    conjunction clauses are required. *)
Lemma generic_satisfiable_conj2 :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall l : list F,
    generic_satisfiable S
      (fun p => p = generic_list_conj2 C l) <->
    generic_satisfiable S (fun p => In p l).
Proof.
  intros M F C S Htop Hand l; split.
  - intros [m Hsingleton]. exists m. constructor.
    intros p HpIn.
    apply (proj1 (generic_models_list_conj2 Htop Hand m l)).
    apply (generic_models_set_elim Hsingleton
      (p := generic_list_conj2 C l)). reflexivity.
    exact HpIn.
  - intros [m Hlist]. exists m. constructor.
    intros p Hp. subst p.
    apply (proj2 (generic_models_list_conj2 Htop Hand m l)).
    intros q Hq. exact (generic_models_set_elim Hlist Hq).
Qed.

(** Source declaration 35/67: [Semantics.satisfiable_fconj].  Its Finset is
    the same duplicate-insensitive list representation; only top and
    conjunction clauses are required. *)
Lemma generic_satisfiable_finset_conj :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_top C S ->
    generic_semantics_and C S ->
    forall s : list F,
    generic_satisfiable S
      (fun p => p = generic_list_conj2 C s) <->
    generic_satisfiable S (fun p => In p s).
Proof. exact generic_satisfiable_conj2. Qed.

(** Source declaration 36/67:
    [Semantics.satisfiableSet_iff_models_nonempty]. *)
Lemma generic_satisfiable_iff_models_nonempty :
  forall (M F : Type) (S : generic_semantics M F) (T : F -> Prop),
    generic_satisfiable S T <->
    exists m : M, generic_model_set S T m.
Proof. reflexivity. Qed.

(** Source declaration 37/67: [Semantics.ModelsSet.models]. *)
Lemma generic_models_set_models :
  forall (M F : Type) (S : generic_semantics M F)
         (T : F -> Prop) (m : M) (p : F),
    generic_models_set S m T -> T p -> generic_models S m p.
Proof.
  intros M F S T m p Hmodels Hp.
  exact (generic_models_set_elim Hmodels Hp).
Qed.

(** Source declaration 38/67: [Semantics.ModelsSet.of_subset]. *)
Lemma generic_models_set_of_subset :
  forall (M F : Type) (S : generic_semantics M F)
         (T U : F -> Prop) (m : M),
    generic_models_set S m U ->
    (forall p : F, T p -> U p) ->
    generic_models_set S m T.
Proof.
  intros M F S T U m HU Hsubset. constructor.
  intros p Hp. apply (generic_models_set_elim HU).
  now apply Hsubset.
Qed.

(** Source declaration 39/67: [Semantics.ModelsSet.of_subset'].  Explicit
    records collapse the source's instance-argument variant to a public alias,
    retained to preserve the source surface. *)
Lemma generic_models_set_of_subset_implicit :
  forall (M F : Type) (S : generic_semantics M F)
         (T U : F -> Prop) (m : M),
    generic_models_set S m U ->
    (forall p : F, T p -> U p) ->
    generic_models_set S m T.
Proof. exact generic_models_set_of_subset. Qed.

(** Source declaration 40/67: the [ModelsSet.empty'] instance. *)
Definition generic_models_set_empty_instance :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    generic_models_set S m (fun _ : F => False).
Proof.
  intros M F S m. constructor. intros p Hempty. contradiction.
Defined.

(** Source declaration 41/67: [Semantics.ModelsSet.empty]. *)
Lemma generic_models_set_empty :
  forall (M F : Type) (S : generic_semantics M F) (m : M),
    generic_models_set S m (fun _ : F => False).
Proof. exact generic_models_set_empty_instance. Qed.

(** Source declaration 42/67: [Semantics.ModelsSet.singleton_iff]. *)
Lemma generic_models_set_singleton_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (m : M) (p : F),
    generic_models_set S m (fun q => q = p) <->
    generic_models S m p.
Proof.
  intros M F S m p; split.
  - intro Hset. apply (generic_models_set_elim Hset). reflexivity.
  - intro Hp. constructor. intros q Hq. now subst q.
Qed.

(** Source declaration 43/67: [Semantics.ModelsSet.insert_iff]. *)
Lemma generic_models_set_insert_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (T : F -> Prop) (m : M) (p : F),
    generic_models_set S m (fun q => q = p \/ T q) <->
    generic_models S m p /\ generic_models_set S m T.
Proof.
  intros M F S T m p; split.
  - intro Hset; split.
    + apply (generic_models_set_elim Hset). now left.
    + constructor. intros q Hq.
      apply (generic_models_set_elim Hset). now right.
  - intros [Hp HT]. constructor. intros q [Hq | Hq].
    + now subst q.
    + exact (generic_models_set_elim HT Hq).
Qed.

(** Source declaration 44/67: [Semantics.ModelsSet.union_iff]. *)
Lemma generic_models_set_union_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (T U : F -> Prop) (m : M),
    generic_models_set S m (fun p => T p \/ U p) <->
    generic_models_set S m T /\ generic_models_set S m U.
Proof.
  intros M F S T U m; split.
  - intro Hunion; split; constructor; intros p Hp;
      apply (generic_models_set_elim Hunion).
    + now left.
    + now right.
  - intros [HT HU]. constructor. intros p [Hp | Hp].
    + exact (generic_models_set_elim HT Hp).
    + exact (generic_models_set_elim HU Hp).
Qed.

(** Source declaration 45/67: [Semantics.ModelsSet.image_iff]. *)
Lemma generic_models_set_image_iff :
  forall (M F I : Type) (S : generic_semantics M F)
         (f : I -> F) (A : I -> Prop) (m : M),
    generic_models_set S m
      (fun p => exists i : I, A i /\ f i = p) <->
    forall i : I, A i -> generic_models S m (f i).
Proof.
  intros M F I S f A m; split.
  - intros Himage i Hi. apply (generic_models_set_elim Himage).
    exists i. now split.
  - intro Hall. constructor. intros p [i [Hi Hfi]].
    rewrite <- Hfi. now apply Hall.
Qed.

(** Source declaration 46/67: [Semantics.ModelsSet.range_iff]. *)
Lemma generic_models_set_range_iff :
  forall (M F I : Type) (S : generic_semantics M F)
         (f : I -> F) (m : M),
    generic_models_set S m
      (fun p => exists i : I, f i = p) <->
    forall i : I, generic_models S m (f i).
Proof.
  intros M F I S f m; split.
  - intros Hrange i. apply (generic_models_set_elim Hrange).
    now exists i.
  - intro Hall. constructor. intros p [i Hfi].
    rewrite <- Hfi. apply Hall.
Qed.

(** Source declaration 47/67: [Semantics.ModelsSet.setOf_iff]. *)
Lemma generic_models_set_predicate_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (P : F -> Prop) (m : M),
    generic_models_set S m P <->
    forall p : F, P p -> generic_models S m p.
Proof.
  intros M F S P m. apply generic_models_set_iff.
Qed.

(** Source declaration 48/67: [Semantics.valid_neg_iff]. *)
Lemma generic_valid_neg_iff :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_neg C S -> forall p : F,
    generic_valid S (generic_neg C p) <->
    ~ generic_satisfiable S (fun q => q = p).
Proof.
  intros M F C S [Hneg] p; split.
  - intros Hvalid [m Hsingleton].
    apply (proj1 (Hneg m p) (Hvalid m)).
    apply (proj1 (generic_models_set_singleton_iff S m p)).
    exact Hsingleton.
  - intros Hunsat m. apply (proj2 (Hneg m p)). intro Hp.
    apply Hunsat. exists m.
    apply (proj2 (generic_models_set_singleton_iff S m p)).
    exact Hp.
Qed.

(** Source declaration 49/67: [Semantics.Satisfiable.of_subset]. *)
Lemma generic_satisfiable_of_subset :
  forall (M F : Type) (S : generic_semantics M F)
         (T U : F -> Prop),
    generic_satisfiable S U ->
    (forall p : F, T p -> U p) ->
    generic_satisfiable S T.
Proof.
  intros M F S T U [m HU] Hsubset.
  exists m. now apply (generic_models_set_of_subset HU).
Qed.

(** Source declaration 50/67: the lifted [Semantics (Set M) F] instance. *)
Definition generic_set_semantics {M F : Type}
    (S : generic_semantics M F) :
    generic_semantics (M -> Prop) F :=
  {| generic_models :=
       fun X p => forall m : M, X m -> generic_models S m p |}.

(** Source declaration 51/67: [Semantics.empty_models]. *)
Lemma generic_empty_models :
  forall (M F : Type) (S : generic_semantics M F) (p : F),
    generic_models (generic_set_semantics S)
      (fun _ : M => False) p.
Proof.
  intros M F S p m Hempty. contradiction.
Qed.

(** Source declaration 52/67: [Semantics.Consequence]. *)
Definition generic_consequence {M F : Type}
    (S : generic_semantics M F) (T : F -> Prop) (p : F) : Prop :=
  generic_models (generic_set_semantics S)
    (generic_model_set S T) p.

(** Source declaration 53/67: [Semantics.set_models_iff]. *)
Lemma generic_set_models_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (X : M -> Prop) (p : F),
    generic_models (generic_set_semantics S) X p <->
    forall m : M, X m -> generic_models S m p.
Proof. reflexivity. Qed.

(** Source declaration 54/67: the lifted [Semantics.Top (Set M)] instance.
    Requiring only the top clause strengthens the source's bundled-instance
    formulation. *)
Definition generic_set_semantics_top {M F : Type}
    (C : generic_connectives F) (S : generic_semantics M F)
    (Htop : generic_semantics_top C S) :
    generic_semantics_top C (generic_set_semantics S).
Proof.
  destruct Htop as [Htop]. constructor.
  intros X m Hm. apply Htop.
Defined.

(** Source declaration 55/67: [Semantics.set_meaningful_iff_nonempty].
    The source's [LogicalConnective] parameter is unused and is omitted. *)
Lemma generic_set_meaningful_iff_nonempty :
  forall (M F : Type) (S : generic_semantics M F),
    (forall m : M, generic_meaningful S m) ->
    forall X : M -> Prop,
    generic_meaningful (generic_set_semantics S) X <->
    exists m : M, X m.
Proof.
  intros M F S HallMeaningful X; split.
  - intros [Hcounter]. destruct Hcounter as [p Hnotall].
    apply NNPP. intro Hempty.
    apply Hnotall. intros m Hm. exfalso.
    apply Hempty. now exists m.
  - intros [m Hm]. destruct (HallMeaningful m) as [Hcounter].
    destruct Hcounter as [p Hnotp].
    constructor. exists p. intro Hall.
    exact (Hnotp (Hall m Hm)).
Qed.

(** Source declaration 56/67:
    [Semantics.meaningful_iff_satisfiableSet].  As in declaration 55, the
    source's unused connective parameter is generalized away. *)
Lemma generic_meaningful_iff_satisfiable :
  forall (M F : Type) (S : generic_semantics M F),
    (forall m : M, generic_meaningful S m) ->
    forall T : F -> Prop,
    generic_satisfiable S T <->
    generic_meaningful (generic_set_semantics S)
      (generic_model_set S T).
Proof.
  intros M F S HallMeaningful T.
  rewrite (generic_set_meaningful_iff_nonempty HallMeaningful
    (generic_model_set S T)).
  apply generic_satisfiable_iff_models_nonempty.
Qed.

(** Source declaration 57/67: [Semantics.consequence_iff]. *)
Lemma generic_consequence_iff :
  forall (M F : Type) (S : generic_semantics M F)
         (T : F -> Prop) (p : F),
    generic_consequence S T p <->
    forall m : M,
      generic_models_set S m T -> generic_models S m p.
Proof. reflexivity. Qed.

(** Source declaration 58/67: [Semantics.consequence_iff'].  Coq's explicit
    record hypotheses collapse the source's instance-argument spelling to
    this retained public alias. *)
Lemma generic_consequence_iff_explicit :
  forall (M F : Type) (S : generic_semantics M F)
         (T : F -> Prop) (p : F),
    generic_consequence S T p <->
    forall m : M,
      generic_models_set S m T -> generic_models S m p.
Proof. exact generic_consequence_iff. Qed.

(** Source declaration 59/67:
    [Semantics.consequence_iff_not_satisfiable].  Only negation's Tarski
    clause is needed; eliminating double negation in the reverse direction is
    classical. *)
Lemma generic_consequence_iff_not_satisfiable :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_semantics_neg C S ->
    forall (T : F -> Prop) (p : F),
    generic_consequence S T p <->
    ~ generic_satisfiable S
      (fun q => q = generic_neg C p \/ T q).
Proof.
  intros M F C S [Hneg] T p; split.
  - intros Hconsequence [m Hinsert].
    pose proof (proj1
      (generic_models_set_insert_iff S T m (generic_neg C p))
      Hinsert) as [Hnegp HT].
    apply (proj1 (Hneg m p) Hnegp).
    exact (Hconsequence m HT).
  - intros Hunsat m HT. apply NNPP. intro Hnotp.
    apply Hunsat. exists m.
    apply (proj2
      (generic_models_set_insert_iff S T m (generic_neg C p))).
    split.
    + now apply (proj2 (Hneg m p)).
    + exact HT.
Qed.

(** Source declaration 60/67: [Semantics.weakening]. *)
Lemma generic_consequence_weakening :
  forall (M F : Type) (S : generic_semantics M F)
         (T U : F -> Prop) (p : F),
    generic_consequence S T p ->
    (forall q : F, T q -> U q) ->
    generic_consequence S U p.
Proof.
  intros M F S T U p HTU Hsubset m HU.
  apply HTU. eapply generic_models_set_of_subset.
  - exact HU.
  - exact Hsubset.
Qed.

(** Source declaration 61/67: [Semantics.of_mem]. *)
Lemma generic_consequence_of_mem :
  forall (M F : Type) (S : generic_semantics M F)
         (T : F -> Prop) (p : F),
    T p -> generic_consequence S T p.
Proof.
  intros M F S T p Hp m Hmodels.
  exact (generic_models_set_elim Hmodels Hp).
Qed.

(** * Cumulative theories and semantic compactness *)

(** Source declaration 62/67: [LO.Cumulative]. *)
Definition generic_cumulative {F : Type}
    (T : nat -> F -> Prop) : Prop :=
  forall (n : nat) (p : F), T n p -> T (S n) p.

(** Source declaration 63/67: [Cumulative.subset_of_le]. *)
Lemma generic_cumulative_subset_of_le :
  forall (F : Type) (T : nat -> F -> Prop),
    generic_cumulative T ->
    forall n k : nat, n <= k ->
    forall p : F, T n p -> T k p.
Proof.
  intros F T Hcumulative n k Hle.
  induction Hle as [|k Hle IH].
  - intros p Hp. exact Hp.
  - intros p Hp. apply Hcumulative. now apply IH.
Qed.

(** Unnumbered infrastructure: both stages embed in their maximum stage.
    This factors the only max-index calculation needed by finite common-stage
    arguments. *)
Lemma generic_cumulative_subsets_at_max :
  forall (F : Type) (T : nat -> F -> Prop),
    generic_cumulative T ->
    forall n k : nat,
    (forall p : F, T n p -> T (Nat.max n k) p) /\
    (forall p : F, T k p -> T (Nat.max n k) p).
Proof.
  intros F T Hcumulative n k; split; intros p Hp.
  - eapply generic_cumulative_subset_of_le; eauto using Nat.le_max_l.
  - eapply generic_cumulative_subset_of_le; eauto using Nat.le_max_r.
Qed.

(** Source declaration 64/67: [Cumulative.finset_mem].  A source Finset is
    represented by a list.  No decidable equality is needed: duplicates are
    harmless and induction directly produces a common stage. *)
Lemma generic_cumulative_list_common_stage :
  forall (F : Type) (T : nat -> F -> Prop),
    generic_cumulative T ->
    forall u : list F,
    (forall p : F, In p u -> exists n : nat, T n p) ->
    exists n : nat, forall p : F, In p u -> T n p.
Proof.
  intros F T Hcumulative u.
  induction u as [|p u IH].
  - intros _. exists 0. intros q Hq. contradiction.
  - intro Hall.
    destruct (Hall p (or_introl eq_refl)) as [n Hp].
    destruct (IH (fun q Hq => Hall q (or_intror Hq)))
      as [k Hk].
    destruct (generic_cumulative_subsets_at_max Hcumulative n k)
      as [Hn Hkmax].
    exists (Nat.max n k). intros q [Hq | Hq].
    + subst q. now apply Hn.
    + apply Hkmax. now apply Hk.
Qed.

(** Source declaration 65/67: [LO.Compact].  Finite subsets are extensional
    lists, so the record quantifies over a list and its predicate inclusion in
    the ambient theory. *)
Record generic_compact {M F : Type}
    (S : generic_semantics M F) : Prop := {
  generic_compact_iff :
    forall T : F -> Prop,
      generic_satisfiable S T <->
      forall u : list F,
        (forall p : F, In p u -> T p) ->
        generic_satisfiable S (fun p => In p u)
}.

(** Unnumbered infrastructure: the contrapositive finite-witness reading of
    compactness.  Its forward direction is classical because it extracts a
    list from a negated universal over all finite contexts; the reverse
    direction is constructive. *)
Lemma generic_compact_unsatisfiable_iff_finite :
  forall (M F : Type) (S : generic_semantics M F),
    generic_compact S -> forall T : F -> Prop,
    ~ generic_satisfiable S T <->
    exists u : list F,
      (forall p : F, In p u -> T p) /\
      ~ generic_satisfiable S (fun p => In p u).
Proof.
  intros M F S [Hcompact] T; split.
  - intro Hunsat.
    destruct (classic
      (exists u : list F,
        (forall p : F, In p u -> T p) /\
        ~ generic_satisfiable S (fun p => In p u)))
      as [Hwitness | Hnone]; [exact Hwitness |].
    exfalso. apply Hunsat. apply (proj2 (Hcompact T)).
    intros u Hu. apply NNPP. intro Hbad.
    apply Hnone. exists u. now split.
  - intros [u [Hu Hbad]] Hsat.
    apply Hbad. eapply generic_satisfiable_of_subset.
    + exact Hsat.
    + exact Hu.
Qed.

(** Unnumbered infrastructure for declaration 66: prune a distinguished
    formula constructively.  The supplied membership proof already decides,
    for every list element, whether it is distinguished or belongs to the
    ambient theory, so no decidable equality on formulas is needed. *)
Lemma list_prune_insert_subset :
  forall (F : Type) (distinguished : F) (T : F -> Prop) (u : list F),
    (forall p : F, In p u -> p = distinguished \/ T p) ->
    exists v : list F,
      (forall p : F, In p v -> T p) /\
      (forall p : F, In p u -> p = distinguished \/ In p v).
Proof.
  intros F distinguished T u.
  induction u as [|x u IH].
  - intro Hsubset. exists nil. split; intros p Hp; contradiction.
  - intro Hsubset.
    assert (Htail : forall p : F, In p u -> p = distinguished \/ T p).
    { intros p Hp. apply Hsubset. now right. }
    destruct (IH Htail) as [v [HvSubset HvCover]].
    destruct (Hsubset x (or_introl eq_refl)) as [Hxd | HxT].
    + exists v. split.
      * exact HvSubset.
      * intros p [Hpx | Hpu].
        -- subst p. left. exact Hxd.
        -- exact (HvCover p Hpu).
    + exists (x :: v). split.
      * intros p [Hpx | Hpv].
        -- subst p. exact HxT.
        -- exact (HvSubset p Hpv).
      * intros p [Hpx | Hpu].
        -- subst p. right. now left.
        -- destruct (HvCover p Hpu) as [Hpd | Hpv].
           ++ now left.
           ++ right. now right.
Qed.

(** Source declaration 66/67: [Compact.conseq_compact].  Only negation's
    Tarski clause is required.  The source's decidable-equality hypothesis is
    generalized away by constructively pruning the finite witness using its
    supplied inclusion proof.  Classical logic is used only through the
    finite unsatisfiable-witness helper above (and the already classical
    consequence/countertheory equivalence). *)
Lemma generic_consequence_compact :
  forall (M F : Type) (C : generic_connectives F)
         (S : generic_semantics M F),
    generic_compact S ->
    generic_semantics_neg C S ->
    forall (T : F -> Prop) (p : F),
    generic_consequence S T p <->
    exists u : list F,
      (forall q : F, In q u -> T q) /\
      generic_consequence S (fun q => In q u) p.
Proof.
  intros M F C S Hcompact Hneg T p; split.
  - intro Hconsequence.
    pose proof (proj1
      (generic_consequence_iff_not_satisfiable Hneg T p)
      Hconsequence) as Hunsat.
    destruct (proj1 (generic_compact_unsatisfiable_iff_finite
      Hcompact (fun q => q = generic_neg C p \/ T q)) Hunsat)
      as [x [HxSubset HxUnsat]].
    destruct (list_prune_insert_subset
      (distinguished := generic_neg C p) (T := T) (u := x) HxSubset)
      as [u [HuSubset HxCover]].
    exists u. split.
    + exact HuSubset.
    + apply (proj2 (generic_consequence_iff_not_satisfiable
        Hneg (fun q => In q u) p)).
      intro HinsertSat. apply HxUnsat.
      eapply generic_satisfiable_of_subset.
      * exact HinsertSat.
      * exact HxCover.
  - intros [u [HuSubset HuConsequence]].
    eapply generic_consequence_weakening.
    + exact HuConsequence.
    + exact HuSubset.
Qed.

(** Source declaration 67/67: [Compact.compact_cumulative].  Predicate union
    is existential stage membership.  The proof is constructive: compactness
    is consumed as a hypothesis, and the list common-stage lemma needs no
    choice or decidable equality. *)
Lemma generic_compact_cumulative :
  forall (M F : Type) (S : generic_semantics M F),
    generic_compact S ->
    forall T : nat -> F -> Prop,
    generic_cumulative T ->
    generic_satisfiable S (fun p => exists n : nat, T n p) <->
    forall n : nat, generic_satisfiable S (T n).
Proof.
  intros M F S [Hcompact] T Hcumulative; split.
  - intros Hunion n. eapply generic_satisfiable_of_subset.
    + exact Hunion.
    + intros p Hp. now exists n.
  - intro Hall. apply (proj2 (Hcompact
      (fun p => exists n : nat, T n p))).
    intros u Hu.
    destruct (generic_cumulative_list_common_stage
      Hcumulative (u := u) Hu) as [n Hstage].
    eapply generic_satisfiable_of_subset.
    + exact (Hall n).
    + exact Hstage.
Qed.
