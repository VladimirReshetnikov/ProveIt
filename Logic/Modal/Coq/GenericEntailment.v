(**
  Generic proof systems and their provability-strength order.

  This module ports declarations 1--48 of the 138 active declaration-producing
  commands in the pinned [Foundation/Logic/Entailment.lean], through
  [Incomparable.of_unprovable].  Foundation distinguishes a Type-valued formal
  proof from the proposition that such a proof is inhabited; that distinction
  is retained here.  In particular, selecting a raw proof from provability is
  deliberately isolated behind informative classical description.

  Foundation defines equivalence by equality of theory predicates.  The Coq
  interface uses its operational pointwise-iff characterization instead.
  Constructively this is a broader relation, but it retains every downstream
  law in the source while avoiding functional and propositional extensionality.
*)

From Stdlib Require Import
  Logic.Classical_Prop Logic.ClassicalChoice Logic.ClassicalEpsilon
  Logic.ChoiceFacts.
From FoundationModal Require Import GenericSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source declaration 1/138: [Entailment]. *)
Record generic_entailment (S F : Type) : Type := {
  generic_proof : S -> F -> Type
}.

Arguments generic_proof {S F} _ _ _.

(** Source declaration 2/138: [Provable]. *)
Definition generic_provable {S F : Type}
    (E : generic_entailment S F) (s : S) (p : F) : Prop :=
  inhabited (generic_proof E s p).

(** Source declaration 3/138: [Unprovable]. *)
Definition generic_unprovable {S F : Type}
    (E : generic_entailment S F) (s : S) (p : F) : Prop :=
  ~ generic_provable E s p.

(** Source declaration 4/138: [PrfSet]. *)
Definition generic_proof_set {S F : Type}
    (E : generic_entailment S F) (s : S) (T : F -> Prop) : Type :=
  forall p, T p -> generic_proof E s p.

(** Source declaration 5/138: [ProvableSet]. *)
Definition generic_provable_set {S F : Type}
    (E : generic_entailment S F) (s : S) (T : F -> Prop) : Prop :=
  forall p, T p -> generic_provable E s p.

(** Source declaration 6/138: [theory]. *)
Definition generic_entailment_theory {S F : Type}
    (E : generic_entailment S F) (s : S) : F -> Prop :=
  generic_provable E s.

(** Source declaration 7/138: [cast]. *)
Definition generic_proof_cast {S F : Type}
    (E : generic_entailment S F) (s : S) (p q : F)
    (b : generic_proof E s p) (e : p = q) : generic_proof E s q :=
  match e with
  | eq_refl => b
  end.

(** Source declaration 8/138: [cast!]. *)
Lemma generic_provable_cast :
  forall (S F : Type) (E : generic_entailment S F) (s : S) (p q : F),
    generic_provable E s p -> p = q -> generic_provable E s q.
Proof.
  intros S F E s p q [b] e; subst q.
  now constructor.
Qed.

Definition generic_empty_type (A : Type) : Prop := forall x : A, False.

(** Source declaration 9/138: [unprovable_iff_isEmpty]. *)
Lemma generic_unprovable_iff_empty_proof :
  forall (S F : Type) (E : generic_entailment S F) (s : S) (p : F),
    generic_unprovable E s p <->
    generic_empty_type (generic_proof E s p).
Proof.
  intros S F E s p; split.
  - intros H b. apply H. now constructor.
  - intros H [b]. exact (H b).
Qed.

(** A reusable, explicit Prop-to-Type boundary.  Keeping the elementary
    inhabited-to-existential conversion in Prop lets informative description
    be the selector's only assumption. *)
Lemma generic_inhabited_exists_true :
  forall A : Type, inhabited A -> exists _ : A, True.
Proof.
  intros A [x]. now exists x.
Qed.

Definition generic_choose_inhabited {A : Type} (h : inhabited A) : A :=
  proj1_sig
    (constructive_indefinite_description (fun _ : A => True)
       (generic_inhabited_exists_true h)).

(** Source declaration 10/138: [Provable.get]. *)
Definition generic_provable_get {S F : Type}
    (E : generic_entailment S F) (s : S) (p : F)
    (h : generic_provable E s p) : generic_proof E s p :=
  generic_choose_inhabited h.

(** Source declaration 11/138: [provableSet_iff].

    The forward implication from pointwise inhabitation to an inhabited
    dependent proof function is precisely functional choice.  It is proved
    independently of the informative selector above, so its assumption audit
    records relational/dependent choice rather than description. *)
Lemma generic_provable_set_iff_inhabited :
  forall (S F : Type) (E : generic_entailment S F) (s : S) (T : F -> Prop),
    generic_provable_set E s T <->
    inhabited (generic_proof_set E s T).
Proof.
  intros S F E s T; split.
  - intro H.
    pose proof
      (functional_choice_to_inhabited_forall_commute ClassicalChoice.choice
        (fun p : F => forall hp : T p, generic_proof E s p)) as Houter.
    apply Houter; intro p.
    pose proof
      (functional_choice_to_inhabited_forall_commute ClassicalChoice.choice
        (fun _ : T p => generic_proof E s p)) as Hinner.
    apply Hinner; intro hp.
    exact (H p hp).
  - intros [b] p hp. constructor. exact (b p hp).
Qed.

(** Source declaration 12/138: [ProvableSet.get]. *)
Definition generic_provable_set_get {S F : Type}
    (E : generic_entailment S F) (s : S) (T : F -> Prop)
    (h : generic_provable_set E s T) : generic_proof_set E s T :=
  fun p hp => generic_choose_inhabited (h p hp).

(** Source declaration 13/138: [WeakerThan]. *)
Record generic_weaker_than {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (s : S) (t : T) : Prop := {
  generic_weaker_subset :
    forall p, generic_provable ES s p -> generic_provable ET t p
}.

(** Source declaration 14/138: [StrictlyWeakerThan]. *)
Record generic_strictly_weaker_than {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (s : S) (t : T) : Prop := {
  generic_strict_weaker : generic_weaker_than ES ET s t;
  generic_strict_not_reverse : ~ generic_weaker_than ET ES t s
}.

(** Source declaration 15/138: [Equiv].  Pointwise equivalence is the source's
    operational characterization and needs no extensionality axiom. *)
Record generic_entailment_equiv {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (s : S) (t : T) : Prop := {
  generic_entailment_equiv_pointwise :
    forall p, generic_provable ES s p <-> generic_provable ET t p
}.

Arguments generic_weaker_subset
  {S T F ES ET s t} _ _ _.
Arguments generic_strict_weaker
  {S T F ES ET s t} _.
Arguments generic_strict_not_reverse
  {S T F ES ET s t} _ _.
Arguments generic_entailment_equiv_pointwise
  {S T F ES ET s t} _ _.

(** Source declaration 16/138: [WeakerThan.refl]. *)
Lemma generic_weaker_than_refl :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_weaker_than E E s s.
Proof. intros S F E s; constructor; auto. Qed.

(** Source declaration 17/138: [WeakerThan.wk]. *)
Lemma generic_weaker_than_weaken :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_weaker_than ES ET s t ->
    forall p, generic_provable ES s p -> generic_provable ET t p.
Proof.
  intros S T F ES ET s t H p Hp.
  exact (generic_weaker_subset H p Hp).
Qed.

(** Source declaration 18/138: [WeakerThan.pbl]. *)
Definition generic_weaker_than_provable := @generic_weaker_than_weaken.

(** Source declaration 19/138: [WeakerThan.trans]. *)
Lemma generic_weaker_than_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_weaker_than ES ET s t ->
    generic_weaker_than ET EU t u ->
    generic_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hst Htu; constructor.
  intros p Hp. apply (generic_weaker_subset Htu p).
  now apply (generic_weaker_subset Hst p).
Qed.

(** Source declaration 20/138: the weak/weak [Trans] instance. *)
Definition generic_weaker_than_trans_instance := @generic_weaker_than_trans.

(** Source declaration 21/138: [weakerThan_iff]. *)
Lemma generic_weaker_than_iff :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_weaker_than ES ET s t <->
    (forall p, generic_provable ES s p -> generic_provable ET t p).
Proof.
  intros S T F ES ET s t; split.
  - intros H p Hp. exact (generic_weaker_subset H p Hp).
  - now constructor.
Qed.

(** Reusable classical counterexample extraction for predicate inclusion. *)
Lemma generic_not_subset_iff_counterexample :
  forall (A : Type) (P Q : A -> Prop),
    ~ (forall x, P x -> Q x) <-> exists x, P x /\ ~ Q x.
Proof.
  intros A P Q; split.
  - intro Hnot.
    destruct (classic (exists x, P x /\ ~ Q x)) as [Hex | Hnone].
    + exact Hex.
    + exfalso. apply Hnot. intros x HP.
      destruct (classic (Q x)) as [HQ | HnQ]; [exact HQ |].
      exfalso. apply Hnone. now exists x.
  - intros [x [HP HnQ]] Hsub. exact (HnQ (Hsub x HP)).
Qed.

(** Source declaration 22/138: [not_weakerThan_iff]. *)
Lemma generic_not_weaker_than_iff :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    ~ generic_weaker_than ES ET s t <->
    exists p, generic_provable ES s p /\ generic_unprovable ET t p.
Proof.
  intros S T F ES ET s t; split.
  - intro Hnot.
    apply (proj1 (generic_not_subset_iff_counterexample
      (fun p => generic_provable ES s p)
      (fun p => generic_provable ET t p))).
    intro Hsubset. apply Hnot. now constructor.
  - intros [p [Hp Hnot]] Hweak.
    exact (Hnot (generic_weaker_subset Hweak p Hp)).
Qed.

(** Source declaration 23/138: [strictlyWeakerThan_iff]. *)
Lemma generic_strictly_weaker_than_iff_witness :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_strictly_weaker_than ES ET s t <->
    (forall p, generic_provable ES s p -> generic_provable ET t p) /\
    exists p, generic_unprovable ES s p /\ generic_provable ET t p.
Proof.
  intros S T F ES ET s t; split.
  - intros [Hweak Hnot]. split.
    + now apply (proj1 (generic_weaker_than_iff ES ET s t)).
    + apply (proj1 (generic_not_weaker_than_iff ET ES t s)) in Hnot.
      destruct Hnot as [p [Hp Hn]]. now exists p.
  - intros [Hweak [p [Hn Hp]]]. constructor.
    + now apply (proj2 (generic_weaker_than_iff ES ET s t)).
    + apply (proj2 (generic_not_weaker_than_iff ET ES t s)).
      now exists p.
Qed.

(** Source declaration 24/138: [swt_of_swt_of_wt]. *)
Lemma generic_strict_weaker_weaker_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_strictly_weaker_than ES ET s t ->
    generic_weaker_than ET EU t u ->
    generic_strictly_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u [Hst Hnot] Htu; constructor.
  - exact (@generic_weaker_than_trans S T U F ES ET EU s t u Hst Htu).
  - intro Hus. apply Hnot.
    exact (@generic_weaker_than_trans T U S F ET EU ES t u s Htu Hus).
Qed.

(** Source declaration 25/138: [swt_of_wt_of_swt]. *)
Lemma generic_weaker_strict_weaker_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_weaker_than ES ET s t ->
    generic_strictly_weaker_than ET EU t u ->
    generic_strictly_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hst [Htu Hnot]; constructor.
  - exact (@generic_weaker_than_trans S T U F ES ET EU s t u Hst Htu).
  - intro Hus. apply Hnot.
    exact (@generic_weaker_than_trans U S T F EU ES ET u s t Hus Hst).
Qed.

(** Source declaration 26/138: strict weakness supplies weakness. *)
Definition generic_weaker_than_of_strictly_weaker
    {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {s : S} {t : T}
    (H : generic_strictly_weaker_than ES ET s t) :
    generic_weaker_than ES ET s t :=
  generic_strict_weaker H.

(** Source declaration 27/138: [StrictlyWeakerThan.trans]. *)
Lemma generic_strictly_weaker_than_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_strictly_weaker_than ES ET s t ->
    generic_strictly_weaker_than ET EU t u ->
    generic_strictly_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hst Htu.
  eapply generic_strict_weaker_weaker_trans; [exact Hst |].
  exact (generic_weaker_than_of_strictly_weaker Htu).
Qed.

(** Source declaration 28/138: the strict/weak [Trans] instance. *)
Definition generic_strict_weaker_weaker_trans_instance :=
  @generic_strict_weaker_weaker_trans.

(** Source declaration 29/138: the weak/strict [Trans] instance. *)
Definition generic_weaker_strict_weaker_trans_instance :=
  @generic_weaker_strict_weaker_trans.

(** Source declaration 30/138: the strict/strict [Trans] instance. *)
Definition generic_strictly_weaker_than_trans_instance :=
  @generic_strictly_weaker_than_trans.

(** Source declaration 31/138: [weakening]. *)
Definition generic_weakening := @generic_weaker_than_weaken.

(** Source declaration 32/138:
    [StrictlyWeakerThan.of_unprovable_provable]. *)
Lemma generic_strictly_weaker_of_unprovable_provable :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T) (p : F),
    generic_weaker_than ES ET s t ->
    generic_unprovable ES s p ->
    generic_provable ET t p ->
    generic_strictly_weaker_than ES ET s t.
Proof.
  intros S T F ES ET s t p Hweak Hnot Hp; constructor.
  - exact Hweak.
  - intro Hreverse. apply Hnot.
    exact (generic_weaker_subset Hreverse p Hp).
Qed.

(** Source declaration 33/138: [Equiv.iff]. *)
Lemma generic_entailment_equiv_iff :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_entailment_equiv ES ET s t <->
    forall p, generic_provable ES s p <-> generic_provable ET t p.
Proof.
  intros S T F ES ET s t; split.
  - exact generic_entailment_equiv_pointwise.
  - now constructor.
Qed.

(** Source declaration 34/138: [Equiv.refl]. *)
Lemma generic_entailment_equiv_refl :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_entailment_equiv E E s s.
Proof. intros S F E s; constructor; tauto. Qed.

(** Source declaration 35/138: [Equiv.symm]. *)
Lemma generic_entailment_equiv_sym :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_entailment_equiv ES ET s t ->
    generic_entailment_equiv ET ES t s.
Proof.
  intros S T F ES ET s t H; constructor; intro p.
  symmetry. exact (generic_entailment_equiv_pointwise H p).
Qed.

(** Source declaration 36/138: [Equiv.trans]. *)
Lemma generic_entailment_equiv_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_entailment_equiv ES ET s t ->
    generic_entailment_equiv ET EU t u ->
    generic_entailment_equiv ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hst Htu; constructor; intro p.
  transitivity (generic_provable ET t p).
  - exact (generic_entailment_equiv_pointwise Hst p).
  - exact (generic_entailment_equiv_pointwise Htu p).
Qed.

(** Source declaration 37/138: [Equiv.antisymm_iff]. *)
Lemma generic_entailment_equiv_iff_mutual_weaker :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_entailment_equiv ES ET s t <->
    generic_weaker_than ES ET s t /\ generic_weaker_than ET ES t s.
Proof.
  intros S T F ES ET s t; split.
  - intros H; split; constructor; intros p Hp.
    + exact (proj1 (generic_entailment_equiv_pointwise H p) Hp).
    + exact (proj2 (generic_entailment_equiv_pointwise H p) Hp).
  - intros [Hst Hts]; constructor; intro p; split; intro Hp.
    + exact (generic_weaker_subset Hst p Hp).
    + exact (generic_weaker_subset Hts p Hp).
Qed.

(** Source declaration 38/138: alias [Equiv.antisymm]. *)
Definition generic_entailment_equiv_of_mutual_weaker
    {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {s : S} {t : T}
    (H : generic_weaker_than ES ET s t /\
         generic_weaker_than ET ES t s) :
    generic_entailment_equiv ES ET s t :=
  proj2 (generic_entailment_equiv_iff_mutual_weaker ES ET s t) H.

(** Source declaration 39/138: [Equiv.le]. *)
Lemma generic_weaker_than_of_equiv :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_entailment_equiv ES ET s t ->
    generic_weaker_than ES ET s t.
Proof.
  intros S T F ES ET s t H.
  apply (proj1 (generic_entailment_equiv_iff_mutual_weaker ES ET s t)) in H.
  exact (proj1 H).
Qed.

(** Source declaration 40/138: the equiv/equiv [Trans] instance. *)
Definition generic_entailment_equiv_trans_instance :=
  @generic_entailment_equiv_trans.

(** Source declaration 41/138: equiv followed by weaker. *)
Lemma generic_equiv_weaker_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_entailment_equiv ES ET s t ->
    generic_weaker_than ET EU t u ->
    generic_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Heq Hweak.
  exact (@generic_weaker_than_trans S T U F ES ET EU s t u
    (generic_weaker_than_of_equiv Heq) Hweak).
Qed.

(** Source declaration 42/138: equiv/equiv viewed as weaker. *)
Lemma generic_equiv_equiv_weaker_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_entailment_equiv ES ET s t ->
    generic_entailment_equiv ET EU t u ->
    generic_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hst Htu.
  apply generic_weaker_than_of_equiv.
  exact (@generic_entailment_equiv_trans S T U F ES ET EU s t u Hst Htu).
Qed.

(** Source declaration 43/138: weaker followed by equiv. *)
Lemma generic_weaker_equiv_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_weaker_than ES ET s t ->
    generic_entailment_equiv ET EU t u ->
    generic_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hweak Heq.
  exact (@generic_weaker_than_trans S T U F ES ET EU s t u
    Hweak (generic_weaker_than_of_equiv Heq)).
Qed.

(** Source declaration 44/138: equiv followed by strict weakness. *)
Lemma generic_equiv_strict_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_entailment_equiv ES ET s t ->
    generic_strictly_weaker_than ET EU t u ->
    generic_strictly_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Heq Hstrict.
  exact (@generic_weaker_strict_weaker_trans S T U F ES ET EU s t u
    (generic_weaker_than_of_equiv Heq) Hstrict).
Qed.

(** Source declaration 45/138: strict weakness followed by equiv. *)
Lemma generic_strict_equiv_trans :
  forall (S T U F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (EU : generic_entailment U F) (s : S) (t : T) (u : U),
    generic_strictly_weaker_than ES ET s t ->
    generic_entailment_equiv ET EU t u ->
    generic_strictly_weaker_than ES EU s u.
Proof.
  intros S T U F ES ET EU s t u Hstrict Heq.
  exact (@generic_strict_weaker_weaker_trans S T U F ES ET EU s t u
    Hstrict (generic_weaker_than_of_equiv Heq)).
Qed.

(** Source declaration 46/138:
    [iff_strictlyWeakerThan_weakerThan_not_equiv].  This characterization is
    constructive when equivalence is represented pointwise. *)
Lemma generic_strictly_weaker_iff_weaker_not_equiv :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_strictly_weaker_than ES ET s t <->
    generic_weaker_than ES ET s t /\
    ~ generic_entailment_equiv ES ET s t.
Proof.
  intros S T F ES ET s t; split.
  - intros [Hweak Hnot]; split; [exact Hweak |].
    intro Heq. apply Hnot.
    pose proof
      (proj1 (generic_entailment_equiv_iff_mutual_weaker ES ET s t) Heq)
      as Hboth.
    exact (proj2 Hboth).
  - intros [Hweak Hneq]; constructor; [exact Hweak |].
    intro Hreverse. apply Hneq.
    apply generic_entailment_equiv_of_mutual_weaker.
    now split.
Qed.

(** Source declaration 47/138: [Incomparable]. *)
Record generic_incomparable {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (s : S) (t : T) : Prop := {
  generic_incomparable_not_left : ~ generic_weaker_than ES ET s t;
  generic_incomparable_not_right : ~ generic_weaker_than ET ES t s
}.

(** Source declaration 48/138: [Incomparable.of_unprovable].  A direct proof
    avoids the source proof's unnecessary appeal to classical counterexample
    extraction. *)
Lemma generic_incomparable_of_unprovable :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    (exists p, generic_provable ES s p /\ generic_unprovable ET t p) ->
    (exists q, generic_provable ET t q /\ generic_unprovable ES s q) ->
    generic_incomparable ES ET s t.
Proof.
  intros S T F ES ET s t [p [Hsp Hntp]] [q [Htq Hnsq]].
  constructor.
  - intro Hst. apply Hntp. exact (generic_weaker_subset Hst p Hsp).
  - intro Hts. apply Hnsq. exact (generic_weaker_subset Hts q Htq).
Qed.
