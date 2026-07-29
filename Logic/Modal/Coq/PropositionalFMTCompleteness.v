(** List-based Hintikka saturation for formula-indexed semantics.

    This is the proof-theoretic half of
    Foundation/Propositional/FMT/Completeness.  Consistent pairs are saturated
    over the duplicate-tolerant subformula enumeration.  The only classical
    step chooses which side preserves consistency; all finite proof algebra is
    supplied constructively by [PropositionalHilbertVFCorsi]. *)

From Stdlib Require Import Lists.List Logic.Classical_Prop
  Logic.ClassicalDescription.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbertVF PropositionalHilbertVFCorsi.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

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
