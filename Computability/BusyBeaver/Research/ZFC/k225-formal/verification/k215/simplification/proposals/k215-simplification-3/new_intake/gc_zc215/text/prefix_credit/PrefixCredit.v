(* Standard-library prototype. NOT compiler-checked in this environment.
   No Admitted, axioms, or imported project-specific scheduler theory.
   Parameters below are the explicit hypotheses of the reusable theorems. *)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Section FiniteCredit.
  Context {A B : Type}.
  Variable lower : A -> B.

  Lemma NoDup_map_on (xs : list A) :
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> lower x = lower y -> x = y) ->
    NoDup (map lower xs).
  Proof.
    intros Hnd. induction Hnd as [|x xs Hfresh Hnd IH]; intros Hinj.
    - constructor.
    - simpl. constructor.
      + intro H. apply in_map_iff in H.
        destruct H as [y [Heq Hy]].
        assert (y = x) as E.
        { apply Hinj; simpl; auto. }
        subst y. contradiction.
      + apply IH. intros a b Ha Hb Heq.
        apply Hinj; simpl; auto.
  Qed.

  (* Sources and destinations are occurrences, not merely command tags.
     Several equal commands at different positions remain distinct. *)
  Theorem finite_prefix_credit (pops : list A) (pushes : list B) :
    NoDup pops ->
    (forall x y, In x pops -> In y pops -> lower x = lower y -> x = y) ->
    (forall x, In x pops -> In (lower x) pushes) ->
    length pops <= length pushes.
  Proof.
    intros Hnd Hinj Hclosed.
    assert (Hmap : NoDup (map lower pops)).
    { apply NoDup_map_on; assumption. }
    assert (Hincl : incl (map lower pops) pushes).
    { intros y Hy. apply in_map_iff in Hy.
      destruct Hy as [x [E Hx]]. subst y. apply Hclosed. exact Hx. }
    assert (Hlen : length (map lower pops) <= length pushes).
    { apply NoDup_incl_length; assumption. }
    rewrite map_length in Hlen. exact Hlen.
  Qed.

  (* Include the imminent pop among the sources but allow only already
     executed pushes as destinations. This proves strict pre-pop credit. *)
  Corollary credit_before_pop (p : A) (past_pops : list A)
      (past_pushes : list B) :
    NoDup (p :: past_pops) ->
    (forall x y, In x (p :: past_pops) -> In y (p :: past_pops) ->
       lower x = lower y -> x = y) ->
    (forall x, In x (p :: past_pops) -> In (lower x) past_pushes) ->
    S (length past_pops) <= length past_pushes.
  Proof.
    intros Hnd Hinj Hclosed.
    exact (finite_prefix_credit (p :: past_pops) past_pushes Hnd Hinj Hclosed).
  Qed.
End FiniteCredit.

Definition Occurrence := (nat * nat)%type.
(* Cut just BEFORE command j of candidate n. *)
Definition before_cut (n j : nat) (x : Occurrence) : Prop :=
  fst x < n \/ (fst x = n /\ snd x < j).

Lemma earlier_candidate_is_in_prefix n j x y :
  before_cut n j x -> fst y < fst x -> before_cut n j y.
Proof.
  unfold before_cut. intros H Hlt. left. destruct H as [H|[H _]]; lia.
Qed.

Lemma earlier_candidate_precedes_command n j y :
  fst y < n -> before_cut n j y.
Proof. intro H. left. exact H. Qed.

(* Candidate-specific specialization: pops enumerates precisely the NIP
   occurrences in a cut; pushes enumerates the DROP occurrences. No bound
   on j is needed for this implication. *)
Section ScheduledCredit.
  Variable Pop Push : Occurrence -> Prop.
  Variable lower : Occurrence -> Occurrence.
  Hypothesis lower_push : forall x, Pop x -> Push (lower x).
  Hypothesis lower_earlier : forall x, Pop x -> fst (lower x) < fst x.
  Hypothesis lower_injective : forall x y, Pop x -> Pop y ->
    lower x = lower y -> x = y.

  Theorem scheduled_prefix_credit n j (pops pushes : list Occurrence) :
    NoDup pops ->
    (forall x, In x pops -> before_cut n j x /\ Pop x) ->
    (forall x, before_cut n j x -> Push x -> In x pushes) ->
    length pops <= length pushes.
  Proof.
    intros Hnd Hpops Hpushes.
    apply (finite_prefix_credit lower pops pushes).
    - exact Hnd.
    - intros x y Hx Hy E.
      destruct (Hpops x Hx) as [_ Hpx].
      destruct (Hpops y Hy) as [_ Hpy].
      apply lower_injective; assumption.
    - intros x Hx. destruct (Hpops x Hx) as [Hcut Hpop].
      apply Hpushes.
      + eapply earlier_candidate_is_in_prefix; [exact Hcut|].
        apply lower_earlier. exact Hpop.
      + apply lower_push. exact Hpop.
  Qed.
End ScheduledCredit.
