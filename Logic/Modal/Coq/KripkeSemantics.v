(**
  Source-facing laws for Kripke semantics.

  This module ports the active mathematical surface of
  [Foundation/Modal/Kripke/Basic.lean].  The recursive interpretation itself,
  substitution, and the relational characterisations of iterated modalities
  already live in [Kripke]; the results below reuse those definitions and add
  the local, model, frame, and frame-class interface supplied by Foundation.

  There is one deliberate representation boundary.  Foundation's [Frame]
  bundles a nonempty world type, whereas [Kripke.frame] permits an empty one.
  Consequently, every assertion that bottom is invalid carries an explicit
  [inhabited_frame] hypothesis.  Counterexample equivalences themselves remain
  valid for empty frames and need no such hypothesis.

  Diamond is defined as [~ box ~].  Results that extract a diamond witness or
  turn failure of a universal statement into a counterexample therefore use
  [Classical_Prop]; the box, implication, monotonicity, and closure laws are
  kept constructive whenever their statements permit it.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence Filtration HilbertKSoundness
  NormalHilbert LogicInfrastructure FrameProperties.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Keep the frame argument visible in this source-facing model API.  Rocq's
    automatic implicit-argument heuristic otherwise hides it because the
    valuation already determines the frame. *)
Arguments model_valid {AtomType} F V p.

(** * Frames and frame classes *)

Definition inhabited_frame (F : frame) : Prop :=
  exists w : World F, True.

Definition kripke_frame_class : Type := frame -> Prop.

Definition kripke_frame_class_valid {AtomType}
    (C : kripke_frame_class) (p : formula AtomType) : Prop :=
  forall F, C F -> valid F p.

Definition kripke_frame_class_validates {AtomType}
    (C : kripke_frame_class) (Gamma : formula AtomType -> Prop) : Prop :=
  forall p, Gamma p -> kripke_frame_class_valid C p.

Definition kripke_frame_class_validates_schema
    (Ax : modal_axiom_schema) (C : kripke_frame_class) : Prop :=
  forall (AtomType : Type) (p : formula AtomType),
    Ax AtomType p -> kripke_frame_class_valid C p.

(** Foundation's whitepoint and blackpoint are exactly the singleton frames
    already used by the soundness development. *)
Definition whitepoint_frame : frame := reflexive_singleton_frame.
Definition blackpoint_frame : frame := irreflexive_singleton_frame.

Lemma whitepoint_inhabited : inhabited_frame whitepoint_frame.
Proof. exists tt; constructor. Qed.

Lemma blackpoint_inhabited : inhabited_frame blackpoint_frame.
Proof. exists tt; constructor. Qed.

Lemma whitepoint_finite : finite_frame whitepoint_frame.
Proof. exists [tt]. intros []; now left. Qed.

Lemma blackpoint_finite : finite_frame blackpoint_frame.
Proof. exists [tt]. intros []; now left. Qed.

Lemma blackpoint_irreflexive : frame_irreflexive blackpoint_frame.
Proof. intros [] H; exact H. Qed.

Lemma blackpoint_transitive : frame_transitive blackpoint_frame.
Proof. exact irreflexive_singleton_transitive. Qed.

Lemma blackpoint_strict_order :
  frame_irreflexive blackpoint_frame /\ frame_transitive blackpoint_frame.
Proof. split; [apply blackpoint_irreflexive | apply blackpoint_transitive]. Qed.

(** * Local satisfaction laws *)

Lemma kripke_satisfies_atom :
  forall (AtomType : Type) F (V : valuation AtomType F) w a,
    satisfies F V w (Atom a) <-> V a w.
Proof. reflexivity. Qed.

Lemma kripke_satisfies_bottom :
  forall (AtomType : Type) F (V : valuation AtomType F) w,
    ~ satisfies F V w (@Bottom AtomType).
Proof. apply satisfies_bottom. Qed.

Lemma kripke_satisfies_imp :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (Imp p q) <->
    (satisfies F V w p -> satisfies F V w q).
Proof. apply satisfies_imp. Qed.

(** Classical: failure of an implication supplies its antecedent. *)
Lemma kripke_not_satisfies_imp :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    ~ satisfies F V w (Imp p q) <->
    satisfies F V w p /\ ~ satisfies F V w q.
Proof. intros; simpl; tauto. Qed.

(** Classical disjunctive reading of implication. *)
Lemma kripke_satisfies_imp_or :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (Imp p q) <->
    ~ satisfies F V w p \/ satisfies F V w q.
Proof. intros; simpl; tauto. Qed.

Lemma kripke_satisfies_or :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (Or p q) <->
    satisfies F V w p \/ satisfies F V w q.
Proof. apply satisfies_or. Qed.

Lemma kripke_satisfies_and :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (And p q) <->
    satisfies F V w p /\ satisfies F V w q.
Proof. apply satisfies_and. Qed.

Lemma kripke_satisfies_neg :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Neg p) <-> ~ satisfies F V w p.
Proof. apply satisfies_neg. Qed.

Lemma kripke_satisfies_top :
  forall (AtomType : Type) F (V : valuation AtomType F) w,
    satisfies F V w (@Top AtomType).
Proof. apply satisfies_top. Qed.

Lemma kripke_satisfies_box :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Box p) <->
    forall u, Rel F w u -> satisfies F V u p.
Proof. apply satisfies_box. Qed.

(** Classical: failure of box produces a successor counterexample. *)
Lemma kripke_not_satisfies_box :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    ~ satisfies F V w (Box p) <->
    exists u, Rel F w u /\ ~ satisfies F V u p.
Proof.
  intros AtomType F V w p; simpl; split.
  - intro Hbox.
    apply NNPP; intro Hnone.
    apply Hbox; intros u Rwu.
    apply NNPP; intro Hnot.
    apply Hnone. exists u; auto.
  - intros [u [Rwu Hnot]] Hbox. exact (Hnot (Hbox u Rwu)).
Qed.

(** Classical witness reading inherited from derived diamond. *)
Lemma kripke_satisfies_dia :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Dia p) <->
    exists u, Rel F w u /\ satisfies F V u p.
Proof. apply satisfies_dia. Qed.

Lemma kripke_not_satisfies_dia :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    ~ satisfies F V w (Dia p) <->
    forall u, Rel F w u -> ~ satisfies F V u p.
Proof.
  intros AtomType F V w p.
  rewrite (@satisfies_dia AtomType F V w p).
  firstorder.
Qed.

Lemma kripke_satisfies_iff :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (Iff p q) <->
    (satisfies F V w p <-> satisfies F V w q).
Proof. apply satisfies_iff. Qed.

(** Classical double-negation elimination. *)
Lemma kripke_satisfies_negneg :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Neg (Neg p)) <-> satisfies F V w p.
Proof. intros; simpl; tauto. Qed.

(** Classical De Morgan law for the derived conjunction. *)
Lemma kripke_not_satisfies_and :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    ~ satisfies F V w (And p q) <->
    ~ satisfies F V w p \/ ~ satisfies F V w q.
Proof.
  intros AtomType F V w p q.
  rewrite (@satisfies_and AtomType F V w p q).
  tauto.
Qed.

(** * Iterated modalities and finite connectives *)

Lemma kripke_satisfies_box_iter_negneg :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p,
    satisfies F V w (box_iter n (Neg (Neg p))) <->
    satisfies F V w (box_iter n p).
Proof.
  intros AtomType F V n w p.
  rewrite !satisfies_box_iter. split; intros H u Hwu.
  - apply (proj1 (@kripke_satisfies_negneg AtomType F V u p)).
    now apply H.
  - apply (proj2 (@kripke_satisfies_negneg AtomType F V u p)).
    now apply H.
Qed.

Lemma kripke_satisfies_box_negneg :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Box (Neg (Neg p))) <-> satisfies F V w (Box p).
Proof.
  intros AtomType F V w p.
  exact (@kripke_satisfies_box_iter_negneg AtomType F V 1 w p).
Qed.

Lemma kripke_satisfies_dia_iter_negneg :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p,
    satisfies F V w (dia_iter n (Neg (Neg p))) <->
    satisfies F V w (dia_iter n p).
Proof.
  intros AtomType F V n w p.
  rewrite !satisfies_dia_iter. split; intros [u [Hwu Hu]]; exists u; split.
  - exact Hwu.
  - now apply (proj1 (@kripke_satisfies_negneg AtomType F V u p)).
  - exact Hwu.
  - now apply (proj2 (@kripke_satisfies_negneg AtomType F V u p)).
Qed.

Lemma kripke_satisfies_dia_negneg :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Dia (Neg (Neg p))) <-> satisfies F V w (Dia p).
Proof.
  intros AtomType F V w p.
  exact (@kripke_satisfies_dia_iter_negneg AtomType F V 1 w p).
Qed.

(** The source's two list conjunction presentations and its Finset
    conjunction are represented by explicit lists.  All statements below are
    duplicate-insensitive, so this loses no mathematical content. *)
Fixpoint kripke_list_disj {AtomType}
    (Gamma : list (formula AtomType)) : formula AtomType :=
  match Gamma with
  | [] => Bottom
  | p :: rest => Or p (kripke_list_disj rest)
  end.

Lemma kripke_satisfies_list_conj :
  forall (AtomType : Type) F (V : valuation AtomType F) w Gamma,
    satisfies F V w (logic_list_conj Gamma) <->
    forall p, In p Gamma -> satisfies F V w p.
Proof.
  intros AtomType F V w Gamma; induction Gamma as [|p rest IH].
  - cbn [logic_list_conj]. firstorder.
  - change
      (satisfies F V w (And p (logic_list_conj rest)) <->
       forall q, In q (p :: rest) -> satisfies F V w q).
    rewrite satisfies_and, IH. split.
    + intros [Hp Hrest] q [Hq | Hq].
      * now subst q.
      * now apply Hrest.
    + intro H. split.
      * apply H. now left.
      * intros q Hq. apply H. now right.
Qed.

Lemma kripke_satisfies_list_conj2 :
  forall (AtomType : Type) F (V : valuation AtomType F) w Gamma,
    satisfies F V w (logic_list_conj2 Gamma) <->
    forall p, In p Gamma -> satisfies F V w p.
Proof.
  intros AtomType F V w Gamma; induction Gamma as [|p rest IH].
  - cbn [logic_list_conj2]. firstorder.
  - destruct rest as [|q rest].
    + change
        (satisfies F V w p <->
         forall q, In q [p] -> satisfies F V w q).
      split.
      * intros Hp q [Hq | Hq]; [now subst q | contradiction].
      * intro H. apply H. now left.
    + change
        (satisfies F V w (And p (logic_list_conj2 (q :: rest))) <->
         forall r, In r (p :: q :: rest) -> satisfies F V w r).
      rewrite satisfies_and, IH. split.
      * intros [Hp Hrest] r [Hr | Hr].
        -- now subst r.
        -- now apply Hrest.
      * intro H. split.
        -- apply H. now left.
        -- intros r Hr. apply H. now right.
Qed.

Lemma kripke_satisfies_list_disj :
  forall (AtomType : Type) F (V : valuation AtomType F) w Gamma,
    satisfies F V w (kripke_list_disj Gamma) <->
    exists p, In p Gamma /\ satisfies F V w p.
Proof.
  intros AtomType F V w Gamma; induction Gamma as [|p rest IH].
  - cbn [kripke_list_disj]. firstorder.
  - change
      (satisfies F V w (Or p (kripke_list_disj rest)) <->
       exists q, In q (p :: rest) /\ satisfies F V w q).
    rewrite satisfies_or, IH. split.
    + intros [Hp | [q [Hq Hsat]]].
      * exists p. split; [now left | exact Hp].
      * exists q. split; [now right | exact Hsat].
    + intros [q [[Hq | Hq] Hsat]].
      * left. now subst q.
      * right. now exists q.
Qed.

Lemma kripke_satisfies_indexed_list_conj :
  forall (I AtomType : Type) F (V : valuation AtomType F) w
      (indices : list I) (f : I -> formula AtomType),
    satisfies F V w (logic_list_conj (map f indices)) <->
    forall i, In i indices -> satisfies F V w (f i).
Proof.
  intros I AtomType F V w indices f.
  rewrite kripke_satisfies_list_conj. split; intros H.
  - intros i Hi. apply H. now apply in_map.
  - intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [i [<- Hi]]. now apply H.
Qed.

Lemma kripke_not_satisfies_indexed_list_conj :
  forall (I AtomType : Type) F (V : valuation AtomType F) w
      (indices : list I) (f : I -> formula AtomType),
    ~ satisfies F V w (logic_list_conj (map f indices)) <->
    exists i, In i indices /\ ~ satisfies F V w (f i).
Proof.
  intros I AtomType F V w indices f.
  rewrite kripke_satisfies_indexed_list_conj.
  induction indices as [|j rest IH].
  - split.
    + intro H. exfalso. apply H. intros i Hi. contradiction.
    + intros [i [Hi _]]. contradiction.
  - split.
    + intro Hnotall.
      destruct (classic (satisfies F V w (f j))) as [Hj | Hnj].
      * assert (Hnotrest :
          ~ (forall i, In i rest -> satisfies F V w (f i))).
        { intro Hrest. apply Hnotall. intros i [Hi | Hi].
          - now subst i.
          - now apply Hrest. }
        destruct (proj1 IH Hnotrest) as [i [Hi Hni]].
        exists i. split; [now right | exact Hni].
      * exists j. split; [now left | exact Hnj].
    + intros [i [[Hi | Hi] Hni]] Hall.
      * apply Hni. subst i. apply Hall. now left.
      * apply Hni. apply Hall. now right.
Qed.

Lemma kripke_satisfies_indexed_list_disj :
  forall (I AtomType : Type) F (V : valuation AtomType F) w
      (indices : list I) (f : I -> formula AtomType),
    satisfies F V w (kripke_list_disj (map f indices)) <->
    exists i, In i indices /\ satisfies F V w (f i).
Proof.
  intros I AtomType F V w indices f.
  rewrite kripke_satisfies_list_disj. split; intros H.
  - destruct H as [p [Hp Hsat]]. apply in_map_iff in Hp.
    destruct Hp as [i [<- Hi]]. now exists i.
  - destruct H as [i [Hi Hsat]]. exists (f i); split; [now apply in_map |].
    exact Hsat.
Qed.

Lemma kripke_not_satisfies_indexed_list_disj :
  forall (I AtomType : Type) F (V : valuation AtomType F) w
      (indices : list I) (f : I -> formula AtomType),
    ~ satisfies F V w (kripke_list_disj (map f indices)) <->
    forall i, In i indices -> ~ satisfies F V w (f i).
Proof.
  intros I AtomType F V w indices f.
  rewrite kripke_satisfies_indexed_list_disj. firstorder.
Qed.

(** * Local closure, congruence, and modal duality *)

Lemma kripke_satisfies_imp_trans :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q r,
    satisfies F V w (Imp p q) ->
    satisfies F V w (Imp q r) ->
    satisfies F V w (Imp p r).
Proof. intros; simpl in *; firstorder. Qed.

Lemma kripke_satisfies_mp :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    satisfies F V w (Imp p q) ->
    satisfies F V w p -> satisfies F V w q.
Proof. intros; simpl in *; firstorder. Qed.

Lemma kripke_neg_semiequiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (satisfies F V w p -> satisfies F V w q) ->
    satisfies F V w (Neg q) -> satisfies F V w (Neg p).
Proof. intros; simpl in *; firstorder. Qed.

Lemma kripke_box_iter_semiequiv :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p q,
    (forall u, rel_iter (Rel F) n w u ->
      satisfies F V u p -> satisfies F V u q) ->
    satisfies F V w (box_iter n p) ->
    satisfies F V w (box_iter n q).
Proof.
  intros AtomType F V n w p q Hpq Hbox.
  apply (proj2 (@satisfies_box_iter AtomType F V n w q)).
  intros u Hwu. apply Hpq; [exact Hwu |].
  now apply (proj1 (@satisfies_box_iter AtomType F V n w p)).
Qed.

Lemma kripke_box_semiequiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (forall u, Rel F w u -> satisfies F V u p -> satisfies F V u q) ->
    satisfies F V w (Box p) -> satisfies F V w (Box q).
Proof.
  intros AtomType F V w p q Hpq Hbox.
  apply (proj2 (@satisfies_box AtomType F V w q)).
  intros u Rwu. apply Hpq; [exact Rwu |].
  now apply (proj1 (@satisfies_box AtomType F V w p)).
Qed.

Lemma kripke_dia_iter_semiequiv :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p q,
    (forall u, rel_iter (Rel F) n w u ->
      satisfies F V u p -> satisfies F V u q) ->
    satisfies F V w (dia_iter n p) ->
    satisfies F V w (dia_iter n q).
Proof.
  intros AtomType F V n w p q Hpq Hdia.
  apply (proj2 (@satisfies_dia_iter AtomType F V n w q)).
  destruct (proj1 (@satisfies_dia_iter AtomType F V n w p) Hdia)
    as [u [Hwu Hu]].
  exists u. split; [exact Hwu | now apply Hpq].
Qed.

Lemma kripke_dia_semiequiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (forall u, Rel F w u -> satisfies F V u p -> satisfies F V u q) ->
    satisfies F V w (Dia p) -> satisfies F V w (Dia q).
Proof.
  intros AtomType F V w p q Hpq Hdia.
  apply (proj2 (@satisfies_dia AtomType F V w q)).
  destruct (proj1 (@satisfies_dia AtomType F V w p) Hdia)
    as [u [Rwu Hu]].
  exists u. split; [exact Rwu | now apply Hpq].
Qed.

Lemma kripke_neg_equiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (satisfies F V w p <-> satisfies F V w q) ->
    (satisfies F V w (Neg p) <-> satisfies F V w (Neg q)).
Proof. intros; simpl in *; tauto. Qed.

Lemma kripke_box_iter_equiv :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p q,
    (forall u, rel_iter (Rel F) n w u ->
      (satisfies F V u p <-> satisfies F V u q)) ->
    (satisfies F V w (box_iter n p) <->
     satisfies F V w (box_iter n q)).
Proof.
  intros AtomType F V n w p q Heq. split; apply kripke_box_iter_semiequiv;
    intros u Hwu; specialize (Heq u Hwu); tauto.
Qed.

Lemma kripke_box_equiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (forall u, Rel F w u ->
      (satisfies F V u p <-> satisfies F V u q)) ->
    (satisfies F V w (Box p) <-> satisfies F V w (Box q)).
Proof.
  intros AtomType F V w p q Heq. split; apply kripke_box_semiequiv;
    intros u Rwu; specialize (Heq u Rwu); tauto.
Qed.

Lemma kripke_dia_iter_equiv :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p q,
    (forall u, rel_iter (Rel F) n w u ->
      (satisfies F V u p <-> satisfies F V u q)) ->
    (satisfies F V w (dia_iter n p) <->
     satisfies F V w (dia_iter n q)).
Proof.
  intros AtomType F V n w p q Heq. split; apply kripke_dia_iter_semiequiv;
    intros u Hwu; specialize (Heq u Hwu); tauto.
Qed.

Lemma kripke_dia_equiv :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    (forall u, Rel F w u ->
      (satisfies F V u p <-> satisfies F V u q)) ->
    (satisfies F V w (Dia p) <-> satisfies F V w (Dia q)).
Proof.
  intros AtomType F V w p q Heq. split; apply kripke_dia_semiequiv;
    intros u Rwu; specialize (Heq u Rwu); tauto.
Qed.

Lemma kripke_dia_dual :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Dia p) <-> satisfies F V w (Neg (Box (Neg p))).
Proof. reflexivity. Qed.

Lemma kripke_dia_iter_dual :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p,
    satisfies F V w (dia_iter n p) <->
    satisfies F V w (Neg (box_iter n (Neg p))).
Proof.
  intros AtomType F V n w p.
  rewrite satisfies_dia_iter, satisfies_neg, satisfies_box_iter.
  split.
  - intros [u [Hwu Hu]] Hbox. exact (Hbox u Hwu Hu).
  - intro Hnotbox. apply NNPP. intro Hnodia. apply Hnotbox.
    intros u Hwu Hu. apply Hnodia. exists u. auto.
Qed.

Lemma kripke_box_dual :
  forall (AtomType : Type) F (V : valuation AtomType F) w p,
    satisfies F V w (Box p) <-> satisfies F V w (Neg (Dia (Neg p))).
Proof.
  intros AtomType F V w p.
  rewrite satisfies_neg, satisfies_dia. split.
  - intros Hbox [u [Rwu Hnot]]. exact (Hnot (Hbox u Rwu)).
  - intros Hnotdia u Rwu. apply NNPP. intro Hnot.
    apply Hnotdia. exists u. split; [exact Rwu | exact Hnot].
Qed.

Lemma kripke_box_iter_dual :
  forall (AtomType : Type) F (V : valuation AtomType F) n w p,
    satisfies F V w (box_iter n p) <->
    satisfies F V w (Neg (dia_iter n (Neg p))).
Proof.
  intros AtomType F V n w p.
  rewrite satisfies_box_iter, satisfies_neg, satisfies_dia_iter. split.
  - intros Hbox [u [Hwu Hnot]]. exact (Hnot (Hbox u Hwu)).
  - intros Hnotdia u Hwu. apply NNPP. intro Hnot.
    apply Hnotdia. exists u. split; [exact Hwu | exact Hnot].
Qed.

Lemma kripke_not_imp_iff_and_neg :
  forall (AtomType : Type) F (V : valuation AtomType F) w p q,
    ~ satisfies F V w (Imp p q) <->
    satisfies F V w (And p (Neg q)).
Proof.
  intros AtomType F V w p q.
  rewrite kripke_not_satisfies_imp, satisfies_and, satisfies_neg.
  tauto.
Qed.

Theorem kripke_satisfies_substitute :
  forall (A B : Type) F (V : valuation B F)
      (sigma : A -> formula B) w p,
    satisfies F V w (substitute sigma p) <->
    satisfies F (fun a u => satisfies F V u (sigma a)) w p.
Proof.
  intros A B F V sigma w p.
  apply satisfies_substitute.
Qed.

(** * Validity on a fixed model *)

(** Coq represents a model by a frame and a valuation rather than by a
    separate dependent record.  Thus [model_valid F V] is the direct
    counterpart of Foundation's bundled [ValidOnModel]. *)
Lemma kripke_model_valid_iff :
  forall (AtomType : Type) F (V : valuation AtomType F) p,
    model_valid F V p <-> forall w, satisfies F V w p.
Proof. reflexivity. Qed.

Lemma kripke_model_valid_top :
  forall (AtomType : Type) F (V : valuation AtomType F),
    model_valid F V (@Top AtomType).
Proof. intros AtomType F V w; apply satisfies_top. Qed.

(** Foundation's models are nonempty by construction.  The explicit premise
    below is the corresponding condition for the more general Coq frame. *)
Lemma kripke_model_valid_bottom :
  forall (AtomType : Type) F (V : valuation AtomType F),
    inhabited_frame F -> ~ model_valid F V (@Bottom AtomType).
Proof.
  intros AtomType F V [w _] Hvalid.
  exact (@satisfies_bottom AtomType F V w (Hvalid w)).
Qed.

(** Classical quantifier duality; valid even when the frame is empty. *)
Lemma kripke_model_invalid_iff_exists_world :
  forall (AtomType : Type) F (V : valuation AtomType F) p,
    ~ model_valid F V p <-> exists w, ~ satisfies F V w p.
Proof.
  intros AtomType F V p; split.
  - intro Hinvalid. apply NNPP. intro Hnone. apply Hinvalid.
    intro w. apply NNPP. intro Hnot.
    apply Hnone. now exists w.
  - intros [w Hnot] Hvalid. exact (Hnot (Hvalid w)).
Qed.

Lemma kripke_model_valid_mp :
  forall (AtomType : Type) F (V : valuation AtomType F) p q,
    model_valid F V (Imp p q) ->
    model_valid F V p -> model_valid F V q.
Proof.
  intros AtomType F V p q Hpq Hp w.
  exact (Hpq w (Hp w)).
Qed.

Lemma kripke_model_valid_nec :
  forall (AtomType : Type) F (V : valuation AtomType F) p,
    model_valid F V p -> model_valid F V (Box p).
Proof. intros AtomType F V p Hp w u _; apply Hp. Qed.

Lemma kripke_model_valid_multinec :
  forall (AtomType : Type) F (V : valuation AtomType F) n p,
    model_valid F V p -> model_valid F V (box_iter n p).
Proof.
  intros AtomType F V n p Hp w.
  apply (proj2 (@satisfies_box_iter AtomType F V n w p)).
  intros u _. apply Hp.
Qed.

Lemma kripke_model_valid_Hilbert_imply_K :
  forall (AtomType : Type) F (V : valuation AtomType F) p q,
    model_valid F V (Hilbert_imply_K p q).
Proof.
  intros AtomType F V p q w.
  exact (@valid_Hilbert_imply_K AtomType F p q V w).
Qed.

Lemma kripke_model_valid_Hilbert_imply_S :
  forall (AtomType : Type) F (V : valuation AtomType F) p q r,
    model_valid F V (Hilbert_imply_S p q r).
Proof.
  intros AtomType F V p q r w.
  exact (@valid_Hilbert_imply_S AtomType F p q r V w).
Qed.

Lemma kripke_model_valid_Hilbert_elim_contra :
  forall (AtomType : Type) F (V : valuation AtomType F) p q,
    model_valid F V (Hilbert_elim_contra p q).
Proof.
  intros AtomType F V p q w.
  exact (@valid_Hilbert_elim_contra AtomType F p q V w).
Qed.

Lemma kripke_model_valid_K :
  forall (AtomType : Type) F (V : valuation AtomType F) p q,
    model_valid F V (K p q).
Proof.
  intros AtomType F V p q w.
  exact (@valid_K AtomType F p q V w).
Qed.

(** * Validity on a frame *)

Definition kripke_frame_validates {AtomType}
    (F : frame) (Gamma : theory AtomType) : Prop :=
  forall p, Gamma p -> valid F p.

Lemma kripke_valid_iff :
  forall (AtomType : Type) F (p : formula AtomType),
    valid F p <-> forall V, model_valid F V p.
Proof. reflexivity. Qed.

Lemma kripke_frame_validates_iff :
  forall (AtomType : Type) F (Gamma : theory AtomType),
    kripke_frame_validates F Gamma <->
    forall p, Gamma p -> valid F p.
Proof. reflexivity. Qed.

Lemma kripke_valid_top :
  forall (AtomType : Type) F, valid F (@Top AtomType).
Proof. intros AtomType F V; apply kripke_model_valid_top. Qed.

Lemma kripke_valid_bottom :
  forall (AtomType : Type) F,
    inhabited_frame F -> ~ valid F (@Bottom AtomType).
Proof.
  intros AtomType F [w _] Hvalid.
  apply (@satisfies_bottom AtomType F (fun _ _ => False) w).
  apply Hvalid.
Qed.

(** Classical quantifier duality; neither result assumes that [F] is
    inhabited. *)
Lemma kripke_not_valid_iff_exists_valuation :
  forall (AtomType : Type) F (p : formula AtomType),
    ~ valid F p <->
    exists V : valuation AtomType F, ~ model_valid F V p.
Proof.
  intros AtomType F p; split.
  - intro Hinvalid. apply NNPP. intro Hnone. apply Hinvalid.
    intros V w. apply NNPP. intro Hnot.
    apply Hnone. exists V. intro Hmodel. exact (Hnot (Hmodel w)).
  - intros [V Hmodel] Hvalid. apply Hmodel. exact (Hvalid V).
Qed.

Lemma kripke_not_valid_iff_exists_valuation_world :
  forall (AtomType : Type) F (p : formula AtomType),
    ~ valid F p <->
    exists V : valuation AtomType F,
      exists w : World F, ~ satisfies F V w p.
Proof.
  intros AtomType F p; split.
  - intro Hinvalid.
    destruct (proj1 (@kripke_not_valid_iff_exists_valuation AtomType F p)
      Hinvalid) as [V Hmodel].
    destruct (proj1
      (@kripke_model_invalid_iff_exists_world AtomType F V p) Hmodel)
      as [w Hnot].
    now exists V, w.
  - intros [V [w Hnot]] Hvalid.
    exact (Hnot (Hvalid V w)).
Qed.

(** Under the unbundled [(F,V)] representation, the source's existential
    model/world view is propositionally the same as valuation/world.  A
    separate theorem name preserves that part of the source interface. *)
Lemma kripke_not_valid_iff_exists_model_world :
  forall (AtomType : Type) F (p : formula AtomType),
    ~ valid F p <->
    exists V : valuation AtomType F,
      exists w : World F, ~ satisfies F V w p.
Proof. apply kripke_not_valid_iff_exists_valuation_world. Qed.

Lemma kripke_valid_mp :
  forall (AtomType : Type) F (p q : formula AtomType),
    valid F (Imp p q) -> valid F p -> valid F q.
Proof. apply valid_mp. Qed.

Lemma kripke_valid_nec :
  forall (AtomType : Type) F (p : formula AtomType),
    valid F p -> valid F (Box p).
Proof. apply valid_nec. Qed.

Lemma kripke_valid_substitute :
  forall (A B : Type) F (p : formula A) (sigma : A -> formula B),
    valid F p -> valid F (substitute sigma p).
Proof. apply valid_substitution. Qed.

Lemma kripke_valid_Hilbert_imply_K :
  forall (AtomType : Type) F (p q : formula AtomType),
    valid F (Hilbert_imply_K p q).
Proof. apply valid_Hilbert_imply_K. Qed.

Lemma kripke_valid_Hilbert_imply_S :
  forall (AtomType : Type) F (p q r : formula AtomType),
    valid F (Hilbert_imply_S p q r).
Proof. apply valid_Hilbert_imply_S. Qed.

Lemma kripke_valid_Hilbert_elim_contra :
  forall (AtomType : Type) F (p q : formula AtomType),
    valid F (Hilbert_elim_contra p q).
Proof. apply valid_Hilbert_elim_contra. Qed.

Lemma kripke_valid_K :
  forall (AtomType : Type) F (p q : formula AtomType),
    valid F (K p q).
Proof. apply valid_K. Qed.

(** * Frame and frame-class logics *)

Definition kripke_frame_logic {AtomType} (F : frame) : theory AtomType :=
  fun p => valid F p.

Definition kripke_frame_class_logic {AtomType}
    (C : kripke_frame_class) : theory AtomType :=
  fun p => kripke_frame_class_valid C p.

Lemma kripke_frame_class_invalid_iff_exists_frame :
  forall (AtomType : Type) (C : kripke_frame_class) (p : formula AtomType),
    ~ kripke_frame_class_valid C p <->
    exists F, C F /\ ~ valid F p.
Proof.
  intros AtomType C p; split.
  - intro Hinvalid. apply NNPP. intro Hnone. apply Hinvalid.
    intros F HF. apply NNPP. intro Hnot.
    apply Hnone. exists F. now split.
  - intros [F [HF Hnot]] Hvalid. exact (Hnot (Hvalid F HF)).
Qed.

Lemma kripke_frame_class_invalid_iff_exists_model :
  forall (AtomType : Type) (C : kripke_frame_class) (p : formula AtomType),
    ~ kripke_frame_class_valid C p <->
    exists F, exists V : valuation AtomType F,
      C F /\ ~ model_valid F V p.
Proof.
  intros AtomType C p; split.
  - intro Hinvalid.
    destruct (proj1
      (@kripke_frame_class_invalid_iff_exists_frame AtomType C p) Hinvalid)
      as [F [HF Hnot]].
    destruct (proj1 (@kripke_not_valid_iff_exists_valuation AtomType F p)
      Hnot) as [V Hmodel].
    exists F, V. now split.
  - intros [F [V [HF Hmodel]]] Hvalid.
    apply Hmodel. exact (Hvalid F HF V).
Qed.

Lemma kripke_frame_class_invalid_iff_exists_model_world :
  forall (AtomType : Type) (C : kripke_frame_class) (p : formula AtomType),
    ~ kripke_frame_class_valid C p <->
    exists F, exists V : valuation AtomType F, exists w : World F,
      C F /\ ~ satisfies F V w p.
Proof.
  intros AtomType C p; split.
  - intro Hinvalid.
    destruct (proj1
      (@kripke_frame_class_invalid_iff_exists_model AtomType C p) Hinvalid)
      as [F [V [HF Hmodel]]].
    destruct (proj1
      (@kripke_model_invalid_iff_exists_world AtomType F V p) Hmodel)
      as [w Hnot].
    exists F, V, w. now split.
  - intros [F [V [w [HF Hnot]]]] Hvalid.
    exact (Hnot (Hvalid F HF V w)).
Qed.

Lemma kripke_frame_class_invalid_iff_exists_valuation_world :
  forall (AtomType : Type) (C : kripke_frame_class) (p : formula AtomType),
    ~ kripke_frame_class_valid C p <->
    exists F, C F /\
      exists V : valuation AtomType F,
        exists w : World F, ~ satisfies F V w p.
Proof.
  intros AtomType C p.
  rewrite (@kripke_frame_class_invalid_iff_exists_model_world AtomType C p).
  split.
  - intros [F [V [w [HF Hnot]]]].
    exists F. split; [exact HF | now exists V, w].
  - intros [F [HF [V [w Hnot]]]].
    exists F, V, w. now split.
Qed.

Lemma kripke_frame_class_validates_with_K :
  forall (AtomType : Type) (C : kripke_frame_class)
      (Gamma : theory AtomType) (a b : AtomType),
    kripke_frame_class_validates C Gamma ->
    kripke_frame_class_validates C
      (theory_insert Gamma (K (Atom a) (Atom b))).
Proof.
  intros AtomType C Gamma a b Hvalid p [Hp | Hp] F HF.
  - subst p. apply valid_K.
  - exact (Hvalid p Hp F HF).
Qed.

(** Literal source corollary: Foundation adjoins K instantiated at atoms 0
    and 1. *)
Corollary kripke_frame_class_validates_with_K_nat :
  forall (C : kripke_frame_class) (Gamma : theory nat),
    kripke_frame_class_validates C Gamma ->
    kripke_frame_class_validates C
      (theory_insert Gamma (K (Atom 0) (Atom 1))).
Proof.
  intros C Gamma Hvalid.
  now apply kripke_frame_class_validates_with_K.
Qed.
