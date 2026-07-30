(** List-based Hintikka saturation for formula-indexed semantics.

    This is the proof-theoretic half of
    Foundation/Propositional/FMT/Completeness.  Consistent pairs are saturated
    over the duplicate-tolerant subformula enumeration.  The only classical
    step chooses which side preserves consistency; all finite proof algebra is
    supplied constructively by [PropositionalHilbertVFCorsi]. *)

From Stdlib Require Import Lists.List Logic.Classical_Prop
  Logic.ClassicalDescription.
From FoundationModal Require Import
  PropositionalFormula PropositionalFMT PropositionalHilbertVF
  PropositionalHilbertVFCorsi.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record phvf_hintikka_pair (Atom : Type) : Type := {
  phvf_hintikka_positive : list (pformula Atom);
  phvf_hintikka_negative : list (pformula Atom)
}.

Arguments phvf_hintikka_positive {Atom} _.
Arguments phvf_hintikka_negative {Atom} _.

Definition phvf_hintikka_consistent {Atom : Type}
    (H : phvf_hilbert Atom) (P : phvf_hintikka_pair Atom) : Prop :=
  ~ phvf_provable H
      (PImp (phvf_list_conj (phvf_hintikka_positive P))
        (phvf_list_disj (phvf_hintikka_negative P))).

Definition phvf_hintikka_insert_positive {Atom : Type}
    (p : pformula Atom) (P : phvf_hintikka_pair Atom) :
    phvf_hintikka_pair Atom :=
  {| phvf_hintikka_positive := p :: phvf_hintikka_positive P;
     phvf_hintikka_negative := phvf_hintikka_negative P |}.

Definition phvf_hintikka_insert_negative {Atom : Type}
    (p : pformula Atom) (P : phvf_hintikka_pair Atom) :
    phvf_hintikka_pair Atom :=
  {| phvf_hintikka_positive := phvf_hintikka_positive P;
     phvf_hintikka_negative := p :: phvf_hintikka_negative P |}.

Definition phvf_proof_hintikka_collapse {Atom : Type}
    {H : phvf_hilbert Atom} {p : pformula Atom}
    {Gamma Delta : list (pformula Atom)}
    (Hpositive : phvf_proof H
      (PImp (PAnd p (phvf_list_conj Gamma)) (phvf_list_disj Delta)))
    (Hnegative : phvf_proof H
      (PImp (phvf_list_conj Gamma)
        (POr p (phvf_list_disj Delta)))) :
    phvf_proof H
      (PImp (phvf_list_conj Gamma) (phvf_list_disj Delta)).
Proof.
  set (G := phvf_list_conj Gamma).
  set (D := phvf_list_disj Delta).
  refine (PHVFPRuleI
    (PHVFPRuleC Hnegative (PHVFPIdentity G)) _).
  refine (PHVFPRuleI phvf_proof_and_comm _).
  refine (PHVFPRuleI (PHVFPDistributeAndOr G p D) _).
  refine (PHVFPRuleI
    (phvf_proof_or_replace_both
      (p := PAnd G p) (p' := PAnd p G)
      (q := PAnd G D) (q' := D)
      phvf_proof_and_comm (PHVFPAndElimR G D)) _).
  exact (PHVFPRuleD Hpositive (PHVFPIdentity D)).
Defined.

Lemma phvf_provable_hintikka_collapse :
  forall (Atom : Type) (H : phvf_hilbert Atom) p Gamma Delta,
    phvf_provable H
      (PImp (PAnd p (phvf_list_conj Gamma)) (phvf_list_disj Delta)) ->
    phvf_provable H
      (PImp (phvf_list_conj Gamma) (POr p (phvf_list_disj Delta))) ->
    phvf_provable H
      (PImp (phvf_list_conj Gamma) (phvf_list_disj Delta)).
Proof.
  intros Atom H p Gamma Delta [Hpositive] [Hnegative]. constructor.
  exact (phvf_proof_hintikka_collapse Hpositive Hnegative).
Qed.

Theorem phvf_hintikka_either_consistent :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) p,
    phvf_hintikka_consistent H P ->
    phvf_hintikka_consistent H (phvf_hintikka_insert_positive p P) \/
    phvf_hintikka_consistent H (phvf_hintikka_insert_negative p P).
Proof.
  intros Atom H P p Hconsistent.
  destruct (classic (phvf_hintikka_consistent H
    (phvf_hintikka_insert_positive p P))) as [Hpos | Hpos].
  - now left.
  - right. intro Hnegative. apply Hconsistent.
    unfold phvf_hintikka_consistent in Hpos, Hnegative.
    cbn in Hpos, Hnegative.
    eapply (@phvf_provable_hintikka_collapse Atom H p
      (phvf_hintikka_positive P) (phvf_hintikka_negative P)).
    + apply NNPP. exact Hpos.
    + exact Hnegative.
Qed.

Definition phvf_hintikka_next {Atom : Type} (H : phvf_hilbert Atom)
    (p : pformula Atom) (P : phvf_hintikka_pair Atom) :
    phvf_hintikka_pair Atom :=
  if excluded_middle_informative
      (phvf_hintikka_consistent H (phvf_hintikka_insert_positive p P))
  then phvf_hintikka_insert_positive p P
  else phvf_hintikka_insert_negative p P.

Lemma phvf_hintikka_next_consistent :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) p,
    phvf_hintikka_consistent H P ->
    phvf_hintikka_consistent H (phvf_hintikka_next H p P).
Proof.
  intros Atom H P p Hconsistent. unfold phvf_hintikka_next.
  destruct (excluded_middle_informative
    (phvf_hintikka_consistent H (phvf_hintikka_insert_positive p P)))
    as [Hpos | Hpos]; [exact Hpos |].
  destruct (@phvf_hintikka_either_consistent Atom H P p Hconsistent)
    as [Hcontra | Hneg]; [contradiction | exact Hneg].
Qed.

Lemma phvf_hintikka_next_positive_monotone :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) p q,
    In q (phvf_hintikka_positive P) ->
    In q (phvf_hintikka_positive (phvf_hintikka_next H p P)).
Proof.
  intros Atom H P p q Hq. unfold phvf_hintikka_next.
  destruct (excluded_middle_informative _); cbn; auto.
Qed.

Lemma phvf_hintikka_next_negative_monotone :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) p q,
    In q (phvf_hintikka_negative P) ->
    In q (phvf_hintikka_negative (phvf_hintikka_next H p P)).
Proof.
  intros Atom H P p q Hq. unfold phvf_hintikka_next.
  destruct (excluded_middle_informative _); cbn; auto.
Qed.

Lemma phvf_hintikka_next_either_member :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) p,
    In p (phvf_hintikka_positive (phvf_hintikka_next H p P)) \/
    In p (phvf_hintikka_negative (phvf_hintikka_next H p P)).
Proof.
  intros Atom H P p. unfold phvf_hintikka_next.
  destruct (excluded_middle_informative _); cbn; auto.
Qed.

Fixpoint phvf_hintikka_enumerate {Atom : Type} (H : phvf_hilbert Atom)
    (P : phvf_hintikka_pair Atom) (Gamma : list (pformula Atom)) :
    phvf_hintikka_pair Atom :=
  match Gamma with
  | [] => P
  | p :: Delta => phvf_hintikka_next H p
      (phvf_hintikka_enumerate H P Delta)
  end.

Lemma phvf_hintikka_enumerate_consistent :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) Gamma,
    phvf_hintikka_consistent H P ->
    phvf_hintikka_consistent H (phvf_hintikka_enumerate H P Gamma).
Proof.
  intros Atom H P Gamma Hconsistent. induction Gamma as [|p Delta IH].
  - exact Hconsistent.
  - cbn. apply phvf_hintikka_next_consistent, IH.
Qed.

Lemma phvf_hintikka_enumerate_positive_monotone :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) Gamma q,
    In q (phvf_hintikka_positive P) ->
    In q (phvf_hintikka_positive (phvf_hintikka_enumerate H P Gamma)).
Proof.
  intros Atom H P Gamma q Hq. induction Gamma as [|p Delta IH].
  - exact Hq.
  - cbn. apply phvf_hintikka_next_positive_monotone, IH.
Qed.

Lemma phvf_hintikka_enumerate_negative_monotone :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) Gamma q,
    In q (phvf_hintikka_negative P) ->
    In q (phvf_hintikka_negative (phvf_hintikka_enumerate H P Gamma)).
Proof.
  intros Atom H P Gamma q Hq. induction Gamma as [|p Delta IH].
  - exact Hq.
  - cbn. apply phvf_hintikka_next_negative_monotone, IH.
Qed.

Lemma phvf_hintikka_enumerate_member :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (P : phvf_hintikka_pair Atom) Gamma p,
    In p Gamma ->
    In p (phvf_hintikka_positive (phvf_hintikka_enumerate H P Gamma)) \/
    In p (phvf_hintikka_negative (phvf_hintikka_enumerate H P Gamma)).
Proof.
  intros Atom H P Gamma. induction Gamma as [|q Delta IH]; intros p Hin.
  - contradiction.
  - cbn. destruct Hin as [<- | Hin].
    + apply phvf_hintikka_next_either_member.
    + destruct (IH p Hin) as [Hpos | Hneg].
      * left. now apply phvf_hintikka_next_positive_monotone.
      * right. now apply phvf_hintikka_next_negative_monotone.
Qed.

Definition phvf_hintikka_saturate {Atom : Type} (H : phvf_hilbert Atom)
    (target : pformula Atom) (P : phvf_hintikka_pair Atom) :
    phvf_hintikka_pair Atom :=
  phvf_hintikka_enumerate H P (pformula_subformulas target).

Record phvf_saturated_hintikka_pair {Atom : Type}
    (H : phvf_hilbert Atom) (target : pformula Atom) : Type := {
  phvf_saturated_pair : phvf_hintikka_pair Atom;
  phvf_saturated_consistent : phvf_hintikka_consistent H phvf_saturated_pair;
  phvf_saturated_complete : forall p,
    pformula_is_subformula p target ->
    In p (phvf_hintikka_positive phvf_saturated_pair) \/
    In p (phvf_hintikka_negative phvf_saturated_pair)
}.

Arguments phvf_saturated_pair {Atom H target} _.

Definition phvf_hintikka_lindenbaum {Atom : Type}
    (H : phvf_hilbert Atom) (target : pformula Atom)
    (P : phvf_hintikka_pair Atom) (Hconsistent : phvf_hintikka_consistent H P) :
    phvf_saturated_hintikka_pair H target.
Proof.
  refine {| phvf_saturated_pair := phvf_hintikka_saturate H target P |}.
  - apply phvf_hintikka_enumerate_consistent, Hconsistent.
  - intros p Hp. apply phvf_hintikka_enumerate_member, Hp.
Defined.

Lemma phvf_hintikka_lindenbaum_positive :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (target : pformula Atom) (P : phvf_hintikka_pair Atom)
      (Hconsistent : phvf_hintikka_consistent H P) p,
    In p (phvf_hintikka_positive P) ->
    In p (phvf_hintikka_positive
      (phvf_saturated_pair
        (@phvf_hintikka_lindenbaum Atom H target P Hconsistent))).
Proof.
  intros. apply phvf_hintikka_enumerate_positive_monotone. assumption.
Qed.

Lemma phvf_hintikka_lindenbaum_negative :
  forall (Atom : Type) (H : phvf_hilbert Atom)
      (target : pformula Atom) (P : phvf_hintikka_pair Atom)
      (Hconsistent : phvf_hintikka_consistent H P) p,
    In p (phvf_hintikka_negative P) ->
    In p (phvf_hintikka_negative
      (phvf_saturated_pair
        (@phvf_hintikka_lindenbaum Atom H target P Hconsistent))).
Proof.
  intros. apply phvf_hintikka_enumerate_negative_monotone. assumption.
Qed.

(** * Consistent saturated-pair closure laws *)

Lemma phvf_saturated_not_both :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p,
    ~ (In p (phvf_hintikka_positive (phvf_saturated_pair W)) /\
       In p (phvf_hintikka_negative (phvf_saturated_pair W))).
Proof.
  intros Atom H target W p [Hpos Hneg].
  apply (@phvf_saturated_consistent Atom H target W).
  destruct (@phvf_provable_list_conj_member Atom H
    (phvf_hintikka_positive (phvf_saturated_pair W)) p Hpos) as [Hleft].
  destruct (@phvf_provable_list_disj_member Atom H
    (phvf_hintikka_negative (phvf_saturated_pair W)) p Hneg) as [Hright].
  constructor. exact (PHVFPRuleI Hleft Hright).
Qed.

Lemma phvf_saturated_positive_iff_not_negative :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p,
    pformula_is_subformula p target ->
    (In p (phvf_hintikka_positive (phvf_saturated_pair W)) <->
     ~ In p (phvf_hintikka_negative (phvf_saturated_pair W))).
Proof.
  intros Atom H target W p Hsub. split.
  - intros Hpos Hneg. exact
      (@phvf_saturated_not_both Atom H target W p (conj Hpos Hneg)).
  - intro Hnotneg. destruct (@phvf_saturated_complete Atom H target W p Hsub)
      as [Hpos | Hneg]; [exact Hpos | contradiction].
Qed.

Lemma phvf_saturated_negative_of_not_positive :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p,
    pformula_is_subformula p target ->
    ~ In p (phvf_hintikka_positive (phvf_saturated_pair W)) ->
    In p (phvf_hintikka_negative (phvf_saturated_pair W)).
Proof.
  intros Atom H target W p Hsub Hnot.
  destruct (@phvf_saturated_complete Atom H target W p Hsub); tauto.
Qed.

Lemma phvf_saturated_imp_closed :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p q,
    pformula_is_subformula p target ->
    pformula_is_subformula q target ->
    phvf_provable H (PImp p q) ->
    In p (phvf_hintikka_positive (phvf_saturated_pair W)) ->
    In q (phvf_hintikka_positive (phvf_saturated_pair W)).
Proof.
  intros Atom H target W p q HpSub HqSub [Hpq] Hp.
  apply NNPP. intro Hnotq.
  pose proof (@phvf_saturated_negative_of_not_positive
    Atom H target W q HqSub Hnotq) as Hq.
  apply (@phvf_saturated_consistent Atom H target W).
  destruct (@phvf_provable_list_conj_member Atom H
    (phvf_hintikka_positive (phvf_saturated_pair W)) p Hp) as [HGp].
  destruct (@phvf_provable_list_disj_member Atom H
    (phvf_hintikka_negative (phvf_saturated_pair W)) q Hq) as [HqD].
  constructor. exact (PHVFPRuleI HGp (PHVFPRuleI Hpq HqD)).
Qed.

Lemma phvf_saturated_bottom_not_positive :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target),
    pformula_is_subformula PFalsum target ->
    ~ In PFalsum (phvf_hintikka_positive (phvf_saturated_pair W)).
Proof.
  intros Atom H target W _ Hbot.
  apply (@phvf_saturated_consistent Atom H target W).
  destruct (@phvf_provable_list_conj_member Atom H
    (phvf_hintikka_positive (phvf_saturated_pair W)) PFalsum Hbot) as [HGbot].
  constructor. exact (PHVFPRuleI HGbot
    (PHVFPEfq (phvf_list_disj
      (phvf_hintikka_negative (phvf_saturated_pair W))))).
Qed.

Lemma phvf_saturated_top_positive :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target),
    pformula_is_subformula ptop target ->
    In ptop (phvf_hintikka_positive (phvf_saturated_pair W)).
Proof.
  intros Atom H target W Hsub. apply NNPP. intro Hnottop.
  pose proof (@phvf_saturated_negative_of_not_positive
    Atom H target W ptop Hsub Hnottop) as Htop.
  apply (@phvf_saturated_consistent Atom H target W).
  destruct (@phvf_provable_list_disj_member Atom H
    (phvf_hintikka_negative (phvf_saturated_pair W)) ptop Htop) as [HtopD].
  constructor. exact (PHVFPRuleI
    (PHVFPFortiori (phvf_list_conj
      (phvf_hintikka_positive (phvf_saturated_pair W)))
      (PHVFPIdentity PFalsum)) HtopD).
Qed.

Theorem phvf_saturated_and_iff :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p q,
    pformula_is_subformula (PAnd p q) target ->
    (In (PAnd p q) (phvf_hintikka_positive (phvf_saturated_pair W)) <->
     In p (phvf_hintikka_positive (phvf_saturated_pair W)) /\
     In q (phvf_hintikka_positive (phvf_saturated_pair W))).
Proof.
  intros Atom H target W p q Hsub.
  destruct (@pformula_subformula_and_components Atom target p q Hsub)
    as [HpSub HqSub]. split.
  - intro Hand. split.
    + eapply (@phvf_saturated_imp_closed Atom H target W (PAnd p q) p);
        [exact Hsub | exact HpSub | | exact Hand].
      constructor. apply PHVFPAndElimL.
    + eapply (@phvf_saturated_imp_closed Atom H target W (PAnd p q) q);
        [exact Hsub | exact HqSub | | exact Hand].
      constructor. apply PHVFPAndElimR.
  - intros [Hp Hq]. apply NNPP. intro Hnotand.
    pose proof (@phvf_saturated_negative_of_not_positive
      Atom H target W (PAnd p q) Hsub Hnotand) as Handneg.
    apply (@phvf_saturated_consistent Atom H target W).
    destruct (@phvf_provable_list_conj_member Atom H
      (phvf_hintikka_positive (phvf_saturated_pair W)) p Hp) as [HGp].
    destruct (@phvf_provable_list_conj_member Atom H
      (phvf_hintikka_positive (phvf_saturated_pair W)) q Hq) as [HGq].
    destruct (@phvf_provable_list_disj_member Atom H
      (phvf_hintikka_negative (phvf_saturated_pair W)) (PAnd p q) Handneg)
      as [HandD].
    constructor. exact (PHVFPRuleI (PHVFPRuleC HGp HGq) HandD).
Qed.

Theorem phvf_saturated_or_iff :
  forall (Atom : Type) (H : phvf_hilbert Atom) target
      (W : phvf_saturated_hintikka_pair H target) p q,
    pformula_is_subformula (POr p q) target ->
    (In (POr p q) (phvf_hintikka_positive (phvf_saturated_pair W)) <->
     In p (phvf_hintikka_positive (phvf_saturated_pair W)) \/
     In q (phvf_hintikka_positive (phvf_saturated_pair W))).
Proof.
  intros Atom H target W p q Hsub.
  destruct (@pformula_subformula_or_components Atom target p q Hsub)
    as [HpSub HqSub]. split.
  - intro Hor. apply NNPP. intro Hneither.
    assert (Hnotp : ~ In p (phvf_hintikka_positive (phvf_saturated_pair W)))
      by tauto.
    assert (Hnotq : ~ In q (phvf_hintikka_positive (phvf_saturated_pair W)))
      by tauto.
    pose proof (@phvf_saturated_negative_of_not_positive
      Atom H target W p HpSub Hnotp) as Hp.
    pose proof (@phvf_saturated_negative_of_not_positive
      Atom H target W q HqSub Hnotq) as Hq.
    apply (@phvf_saturated_consistent Atom H target W).
    destruct (@phvf_provable_list_conj_member Atom H
      (phvf_hintikka_positive (phvf_saturated_pair W)) (POr p q) Hor) as [HGor].
    destruct (@phvf_provable_list_disj_member Atom H
      (phvf_hintikka_negative (phvf_saturated_pair W)) p Hp) as [HpD].
    destruct (@phvf_provable_list_disj_member Atom H
      (phvf_hintikka_negative (phvf_saturated_pair W)) q Hq) as [HqD].
    constructor. exact (PHVFPRuleI HGor (PHVFPRuleD HpD HqD)).
  - intros [Hp | Hq].
    + eapply (@phvf_saturated_imp_closed Atom H target W p (POr p q));
        [exact HpSub | exact Hsub | | exact Hp].
      constructor. apply PHVFPOrIntroL.
    + eapply (@phvf_saturated_imp_closed Atom H target W q (POr p q));
        [exact HqSub | exact Hsub | | exact Hq].
      constructor. apply PHVFPOrIntroR.
Qed.

(** * Formula-indexed Hintikka model

    A fresh semantic root sees every world.  Saturated pairs never access the
    fresh root, so their forcing behavior is governed solely by the Corsi
    implication relation.  This replaces the source's filtered circular root
    and removes its disjunction-property premise from the truth lemma. *)

Definition phvf_fmt_hintikka_access (H : phvf_hilbert@{Set} nat)
    (target indexed : pformula@{Set} nat)
    (x y : option (@phvf_saturated_hintikka_pair nat H target)) : Prop :=
  match x, y with
  | None, _ => True
  | Some _, None => False
  | Some X, Some Y =>
      match indexed with
      | PImp p q =>
          ~ pformula_is_subformula (PImp p q) target \/
          In (PImp p q)
            (phvf_hintikka_negative (phvf_saturated_pair X)) \/
          In p (phvf_hintikka_negative (phvf_saturated_pair Y)) \/
          In q (phvf_hintikka_positive (phvf_saturated_pair Y))
      | _ => True
      end
  end.

Arguments phvf_fmt_hintikka_access H target indexed x y : clear implicits.

Definition phvf_fmt_hintikka_frame
    (H : phvf_hilbert@{Set} nat) (target : pformula@{Set} nat) : fmt_frame :=
  {| fmt_world := option (@phvf_saturated_hintikka_pair nat H target);
     fmt_access := phvf_fmt_hintikka_access H target;
     fmt_root := None;
     fmt_root_access := fun _ _ => I |}.

Arguments phvf_fmt_hintikka_frame H target : clear implicits.

Definition phvf_fmt_hintikka_model
    (H : phvf_hilbert@{Set} nat) (target : pformula@{Set} nat) : fmt_model :=
  {| fmt_model_frame := phvf_fmt_hintikka_frame H target;
     fmt_model_valuation := fun a x =>
       match x with
       | None => False
       | Some W => In (PAtom a)
           (phvf_hintikka_positive (phvf_saturated_pair W))
       end |}.

Arguments phvf_fmt_hintikka_model H target : clear implicits.

Definition phvf_hintikka_imp_seed (p q : pformula@{Set} nat) :
    phvf_hintikka_pair nat :=
  {| phvf_hintikka_positive := [p];
     phvf_hintikka_negative := [q] |}.

Lemma phvf_hintikka_imp_seed_consistent :
  forall (H : phvf_hilbert@{Set} nat) target
      (W : @phvf_saturated_hintikka_pair nat H target) p q,
    pformula_is_subformula (PImp p q) target ->
    ~ In (PImp p q)
        (phvf_hintikka_positive (phvf_saturated_pair W)) ->
    phvf_hintikka_consistent H (phvf_hintikka_imp_seed p q).
Proof.
  intros H target W p q Hsub Hnotpos Hseed.
  pose proof (@phvf_saturated_negative_of_not_positive
    nat H target W (PImp p q) Hsub Hnotpos) as Hnegative.
  unfold phvf_hintikka_consistent, phvf_hintikka_imp_seed in Hseed.
  cbn in Hseed.
  destruct Hseed as [Hseed].
  assert (Hpq : phvf_proof H (PImp p q)).
  { refine (PHVFPRuleI
      (PHVFPRuleC (PHVFPIdentity p)
        (PHVFPFortiori p (PHVFPIdentity PFalsum))) _).
    refine (PHVFPRuleI Hseed _).
    exact (PHVFPRuleD (PHVFPIdentity q) (PHVFPEfq q)). }
  apply (@phvf_saturated_consistent nat H target W).
  destruct (@phvf_provable_list_disj_member nat H
    (phvf_hintikka_negative (phvf_saturated_pair W))
    (PImp p q) Hnegative) as [HimpD].
  constructor. exact (PHVFPRuleI
    (PHVFPFortiori
      (phvf_list_conj
        (phvf_hintikka_positive (phvf_saturated_pair W))) Hpq)
    HimpD).
Qed.

Theorem phvf_fmt_hintikka_truth :
  forall (H : phvf_hilbert@{Set} nat) target p,
    pformula_is_subformula p target ->
    forall W : @phvf_saturated_hintikka_pair nat H target,
      In p (phvf_hintikka_positive (phvf_saturated_pair W)) <->
      fmt_forces (phvf_fmt_hintikka_model H target) (Some W) p.
Proof.
  intros H target p. induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros Hsub W; cbn [phvf_fmt_hintikka_model].
  - reflexivity.
  - split.
    + exact (fun Hp => False_rect _
        (@phvf_saturated_bottom_not_positive nat H target W Hsub Hp)).
    + contradiction.
  - rewrite (@phvf_saturated_and_iff nat H target W p q Hsub).
    destruct (@pformula_subformula_and_components nat target p q Hsub)
      as [HpSub HqSub].
    rewrite (IHp HpSub W), (IHq HqSub W). reflexivity.
  - rewrite (@phvf_saturated_or_iff nat H target W p q Hsub).
    destruct (@pformula_subformula_or_components nat target p q Hsub)
      as [HpSub HqSub].
    rewrite (IHp HpSub W), (IHq HqSub W). reflexivity.
  - destruct (@pformula_subformula_imp_components nat target p q Hsub)
      as [HpSub HqSub]. split.
    + intros Himp Y Haccess Hpforce. destruct Y as [Y|].
      * cbn [phvf_fmt_hintikka_frame phvf_fmt_hintikka_access] in Haccess.
        destruct Haccess as [Hnotsub | [Hnegative | [Hpnegative | Hqpositive]]].
        -- exact (False_rect _ (Hnotsub Hsub)).
        -- exact (False_rect _
             (@phvf_saturated_not_both nat H target W (PImp p q)
               (conj Himp Hnegative))).
        -- pose proof (proj2 (IHp HpSub Y) Hpforce) as Hppositive.
           exact (False_rect _
             (@phvf_saturated_not_both nat H target Y p
               (conj Hppositive Hpnegative))).
        -- exact (proj1 (IHq HqSub Y) Hqpositive).
      * exact (False_rect _ Haccess).
    + intro Hforces. apply NNPP. intro Hnotpos.
      pose proof (@phvf_hintikka_imp_seed_consistent
        H target W p q Hsub Hnotpos) as Hseed.
      set (Y := @phvf_hintikka_lindenbaum nat H target
        (phvf_hintikka_imp_seed p q) Hseed).
      assert (Hppositive : In p
        (phvf_hintikka_positive (phvf_saturated_pair Y))).
      { apply (@phvf_hintikka_lindenbaum_positive nat H target
          (phvf_hintikka_imp_seed p q) Hseed p). cbn. auto. }
      assert (Hqnegative : In q
        (phvf_hintikka_negative (phvf_saturated_pair Y))).
      { apply (@phvf_hintikka_lindenbaum_negative nat H target
          (phvf_hintikka_imp_seed p q) Hseed q). cbn. auto. }
      assert (Haccess : fmt_access
        (fmt_model_frame (phvf_fmt_hintikka_model H target))
        (PImp p q) (Some W) (Some Y)).
      { cbn [phvf_fmt_hintikka_model phvf_fmt_hintikka_frame
          phvf_fmt_hintikka_access].
        right. left. now apply (@phvf_saturated_negative_of_not_positive
          nat H target W (PImp p q) Hsub). }
      pose proof (Hforces (Some Y) Haccess
        (proj1 (IHp HpSub Y) Hppositive)) as Hqforces.
      pose proof (proj2 (IHq HqSub Y) Hqforces) as Hqpositive.
      exact (@phvf_saturated_not_both nat H target Y q
        (conj Hqpositive Hqnegative)).
Qed.

Definition phvf_hintikka_counter_seed (target : pformula@{Set} nat) :
    phvf_hintikka_pair nat :=
  {| phvf_hintikka_positive := [];
     phvf_hintikka_negative := [target] |}.

Lemma phvf_hintikka_counter_seed_consistent :
  forall (H : phvf_hilbert@{Set} nat) target,
    ~ phvf_provable H target ->
    phvf_hintikka_consistent H (phvf_hintikka_counter_seed target).
Proof.
  intros H target Hnot Hseed.
  unfold phvf_hintikka_consistent, phvf_hintikka_counter_seed in Hseed.
  cbn in Hseed. destruct Hseed as [Hseed].
  apply Hnot. constructor.
  exact (PHVFPModusPonens
    (PHVFPRuleD (PHVFPIdentity target) (PHVFPEfq target))
    (PHVFPModusPonens Hseed (PHVFPIdentity PFalsum))).
Qed.

Theorem phvf_provable_of_fmt_hintikka_valid :
  forall (H : phvf_hilbert@{Set} nat) target,
    fmt_model_valid (phvf_fmt_hintikka_model H target) target ->
    phvf_provable H target.
Proof.
  intros H target Hvalid. apply NNPP. intro Hnot.
  pose proof (@phvf_hintikka_counter_seed_consistent H target Hnot) as Hseed.
  set (W := @phvf_hintikka_lindenbaum nat H target
    (phvf_hintikka_counter_seed target) Hseed).
  assert (Hnegative : In target
    (phvf_hintikka_negative (phvf_saturated_pair W))).
  { apply (@phvf_hintikka_lindenbaum_negative nat H target
      (phvf_hintikka_counter_seed target) Hseed target). cbn. auto. }
  pose proof (proj2 (@phvf_fmt_hintikka_truth H target target
    (pformula_subformulas_self target) W) (Hvalid (Some W))) as Hpositive.
  exact (@phvf_saturated_not_both nat H target W target
    (conj Hpositive Hnegative)).
Qed.

Theorem phvf_fmt_complete_all_frames :
  forall H : phvf_hilbert@{Set} nat,
    phvf_fmt_frame_complete H (fun _ => True).
Proof.
  intros H target Hvalid.
  apply (@phvf_provable_of_fmt_hintikka_valid H target).
  intro W. exact (Hvalid (phvf_fmt_hintikka_frame H target) I
    (@fmt_model_valuation (phvf_fmt_hintikka_model H target)) W).
Qed.

Theorem phvf_fmt_hintikka_nt_serial_of_ser :
  forall (H : phvf_hilbert@{Set} nat) target,
    phvf_provable H phvf_axiom_ser ->
    fmt_nt_serial (phvf_fmt_hintikka_frame H target).
Proof.
  intros H target Hser [W|].
  - exists (Some W).
    cbn [phvf_fmt_hintikka_frame phvf_fmt_hintikka_access].
    destruct (classic (pformula_is_subformula (pneg ptop) target))
      as [Hsub | Hnotsub].
    + right. left.
      apply (@phvf_saturated_negative_of_not_positive
        nat H target W (pneg ptop) Hsub).
      intro Hpositive.
      destruct (@pformula_subformula_imp_components nat target ptop PFalsum Hsub)
        as [_ HbotSub].
      pose proof (@phvf_saturated_imp_closed nat H target W
        (pneg ptop) PFalsum Hsub HbotSub Hser Hpositive) as Hbot.
      exact (@phvf_saturated_bottom_not_positive nat H target W HbotSub Hbot).
    + now left.
  - exists None. exact I.
Qed.

Theorem phvf_fmt_complete_nt_serial_of_ser :
  forall (H : phvf_hilbert@{Set} nat),
    phvf_provable H phvf_axiom_ser ->
    phvf_fmt_frame_complete H fmt_nt_serial.
Proof.
  intros H Hser target Hvalid.
  apply (@phvf_provable_of_fmt_hintikka_valid H target).
  intro W. exact (Hvalid (phvf_fmt_hintikka_frame H target)
    (@phvf_fmt_hintikka_nt_serial_of_ser H target Hser)
    (@fmt_model_valuation (phvf_fmt_hintikka_model H target)) W).
Qed.

Corollary phvf_VF_fmt_complete :
  phvf_fmt_frame_complete (phvf_hilbert_VF nat) (fun _ => True).
Proof. apply phvf_fmt_complete_all_frames. Qed.

Corollary phvf_VF_Ser_fmt_complete :
  phvf_fmt_frame_complete (phvf_hilbert_VF_Ser nat) fmt_nt_serial.
Proof.
  apply phvf_fmt_complete_nt_serial_of_ser.
  apply phvf_VF_Ser_provable_ser.
Qed.
