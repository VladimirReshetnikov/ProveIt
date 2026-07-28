(**
  Generic proof systems and their provability-strength order.

  This module ports all 138 active declaration-producing
  commands in the pinned [Foundation/Logic/Entailment.lean], through
  [Pullback.consistent].  Foundation distinguishes a Type-valued formal
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
From FoundationModal Require Import GenericSemantics GenericAdjunctiveSet.

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

(** * Consistency, explosion, and syntactic completeness *)

(** Source declaration 49/138: [provableSet_theory]. *)
Lemma generic_provable_set_theory :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_provable_set E s (generic_entailment_theory E s).
Proof.
  intros S F E s p Hp. exact Hp.
Qed.

(** Source declaration 50/138: [Inconsistent]. *)
Definition generic_inconsistent {S F : Type}
    (E : generic_entailment S F) (s : S) : Prop :=
  forall p, generic_provable E s p.

(** Source declaration 51/138: [Consistent]. *)
Record generic_consistent {S F : Type}
    (E : generic_entailment S F) (s : S) : Prop := {
  generic_consistent_not_inconsistent_field :
    ~ generic_inconsistent E s
}.

Arguments generic_consistent_not_inconsistent_field
  {S F E s} _ _.

(** Source declaration 52/138: [inconsistent_def]. *)
Lemma generic_inconsistent_def :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_inconsistent E s <->
    forall p, generic_provable E s p.
Proof. reflexivity. Qed.

(** Source declaration 53/138: [inconsistent_iff_theory_eq].  Predicate
    equality is represented pointwise, as it was for system equivalence above;
    this removes the source theorem's extensionality boundary. *)
Lemma generic_inconsistent_iff_theory_universal :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_inconsistent E s <->
    forall p, generic_entailment_theory E s p <-> True.
Proof.
  intros S F E s; split.
  - intros H p; split.
    + intros _. exact I.
    + intros _. exact (H p).
  - intros H p. apply (proj2 (H p)). exact I.
Qed.

(** Source declaration 54/138: [not_inconsistent_iff_consistent]. *)
Lemma generic_not_inconsistent_iff_consistent :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    ~ generic_inconsistent E s <-> generic_consistent E s.
Proof.
  intros S F E s; split.
  - intro H. now constructor.
  - intros [H]. exact H.
Qed.

(** Source declaration 55/138: alias [Consistent.not_inc]. *)
Definition generic_consistent_not_inconsistent
    {S F : Type} {E : generic_entailment S F} {s : S}
    (H : generic_consistent E s) : ~ generic_inconsistent E s :=
  generic_consistent_not_inconsistent_field H.

(** Source declaration 56/138: [not_consistent_iff_inconsistent].
    Only the forward implication is classical double-negation elimination. *)
Lemma generic_not_consistent_iff_inconsistent :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    ~ generic_consistent E s <-> generic_inconsistent E s.
Proof.
  intros S F E s; split.
  - intro Hnot.
    apply NNPP. intro Hnot_inconsistent.
    apply Hnot. constructor. exact Hnot_inconsistent.
  - intros Hinc Hcon.
    exact (generic_consistent_not_inconsistent Hcon Hinc).
Qed.

(** Source declaration 57/138: alias [Inconsistent.not_con].  This direction
    is proved directly so it does not inherit declaration 56's classical
    dependency. *)
Lemma generic_inconsistent_not_consistent :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_inconsistent E s -> ~ generic_consistent E s.
Proof.
  intros S F E s Hinc Hcon.
  exact (generic_consistent_not_inconsistent Hcon Hinc).
Qed.

(** Source declaration 58/138: [consistent_iff_exists_unprovable].  The
    counterexample-extraction direction reuses the single classical predicate
    inclusion helper from declaration 22. *)
Lemma generic_consistent_iff_exists_unprovable :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_consistent E s <->
    exists p, generic_unprovable E s p.
Proof.
  intros S F E s; split.
  - intros Hcon.
    assert (Hnot_subset :
      ~ (forall p : F, True -> generic_provable E s p)).
    { intro Hall. apply (generic_consistent_not_inconsistent Hcon).
      intro p. exact (Hall p I). }
    apply (proj1 (@generic_not_subset_iff_counterexample F
      (fun _ => True) (fun p => generic_provable E s p))) in Hnot_subset.
    destruct Hnot_subset as [p [_ Hnot]]. now exists p.
  - intros [p Hnot]. constructor. intro Hinc.
    exact (Hnot (Hinc p)).
Qed.

(** Source declaration 59/138: alias [Consistent.exists_unprovable]. *)
Definition generic_consistent_exists_unprovable
    {S F : Type} {E : generic_entailment S F} {s : S}
    (H : generic_consistent E s) :
    exists p, generic_unprovable E s p :=
  proj1 (generic_consistent_iff_exists_unprovable E s) H.

(** Source declaration 60/138: [Consistent.of_unprovable]. *)
Lemma generic_consistent_of_unprovable :
  forall (S F : Type) (E : generic_entailment S F) (s : S) (p : F),
    generic_unprovable E s p -> generic_consistent E s.
Proof.
  intros S F E s p Hnot. constructor. intro Hinc.
  exact (Hnot (Hinc p)).
Qed.

(** Source declaration 61/138: [inconsistent_iff_theory_eq_univ].  This is
    the source's second name for declaration 53. *)
Lemma generic_inconsistent_iff_theory_universal_alias :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_inconsistent E s <->
    forall p, generic_entailment_theory E s p <-> True.
Proof. exact generic_inconsistent_iff_theory_universal. Qed.

(** Source declaration 62/138: alias [Inconsistent.theory_eq]. *)
Lemma generic_inconsistent_theory_universal :
  forall (S F : Type) (E : generic_entailment S F) (s : S),
    generic_inconsistent E s ->
    forall p, generic_entailment_theory E s p <-> True.
Proof.
  intros S F E s Hinc p; split.
  - intros _. exact I.
  - intros _. exact (Hinc p).
Qed.

(** Source declaration 63/138: [Inconsistent.of_ge]. *)
Lemma generic_inconsistent_of_ge :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_inconsistent ES s ->
    generic_weaker_than ES ET s t ->
    generic_inconsistent ET t.
Proof.
  intros S T F ES ET s t Hinc Hweak p.
  exact (generic_weaker_subset Hweak p (Hinc p)).
Qed.

(** Source declaration 64/138: [Consistent.of_le].  A direct contrapositive
    proof avoids the classical double-negation theorem at declaration 56. *)
Lemma generic_consistent_of_le :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T),
    generic_consistent ES s ->
    generic_weaker_than ET ES t s ->
    generic_consistent ET t.
Proof.
  intros S T F ES ET s t Hcon Hweak. constructor. intro Hinc_t.
  apply (generic_consistent_not_inconsistent Hcon).
  intro p. exact (generic_weaker_subset Hweak p (Hinc_t p)).
Qed.

(** Source declaration 65/138: [DeductiveExplosion].  The capability is
    generalized from a full logical-connective package to the sole operation
    it uses: a distinguished bottom formula. *)
Record generic_deductive_explosion {S F : Type}
    (E : generic_entailment S F) (bottom : F) : Type := {
  generic_deductive_explosion_raw :
    forall s : S,
      generic_proof E s bottom ->
      forall p : F, generic_proof E s p
}.

Arguments generic_deductive_explosion_raw
  {S F E bottom} _ _ _ _.

(** Source declaration 66/138: [DeductiveExplosion.dexp!]. *)
Lemma generic_deductive_explosion_provable :
  forall (S F : Type) (E : generic_entailment S F) (bottom : F),
    generic_deductive_explosion E bottom ->
    forall (s : S),
      generic_provable E s bottom ->
      forall p : F, generic_provable E s p.
Proof.
  intros S F E bottom Hexplosion s [b] p. constructor.
  exact (generic_deductive_explosion_raw Hexplosion s b p).
Qed.

(** Source declaration 67/138: [inconsistent_iff_provable_bot]. *)
Lemma generic_inconsistent_iff_provable_bottom :
  forall (S F : Type) (E : generic_entailment S F) (bottom : F),
    generic_deductive_explosion E bottom ->
    forall s : S,
      generic_inconsistent E s <-> generic_provable E s bottom.
Proof.
  intros S F E bottom Hexplosion s; split.
  - intro Hinc. exact (Hinc bottom).
  - intros Hbottom p.
    exact (@generic_deductive_explosion_provable
      S F E bottom Hexplosion s Hbottom p).
Qed.

(** Source declaration 68/138: alias [inconsistent_of_provable]. *)
Lemma generic_inconsistent_of_provable_bottom :
  forall (S F : Type) (E : generic_entailment S F) (bottom : F),
    generic_deductive_explosion E bottom ->
    forall s : S,
      generic_provable E s bottom -> generic_inconsistent E s.
Proof.
  intros S F E bottom Hexplosion s Hbottom p.
  exact (@generic_deductive_explosion_provable
    S F E bottom Hexplosion s Hbottom p).
Qed.

(** Source declaration 69/138: [consistent_iff_unprovable_bot].  Both
    directions are direct and constructive. *)
Lemma generic_consistent_iff_unprovable_bottom :
  forall (S F : Type) (E : generic_entailment S F) (bottom : F),
    generic_deductive_explosion E bottom ->
    forall s : S,
      generic_consistent E s <-> generic_unprovable E s bottom.
Proof.
  intros S F E bottom Hexplosion s; split.
  - intros Hcon Hbottom.
    apply (generic_consistent_not_inconsistent Hcon).
    intro p.
    exact (@generic_deductive_explosion_provable
      S F E bottom Hexplosion s Hbottom p).
  - intro Hnot_bottom. constructor. intro Hinc.
    exact (Hnot_bottom (Hinc bottom)).
Qed.

(** Source declaration 70/138: alias [Consistent.not_bot].  This is proved
    directly rather than projected through another theorem. *)
Lemma generic_consistent_not_bottom :
  forall (S F : Type) (E : generic_entailment S F) (bottom : F),
    generic_deductive_explosion E bottom ->
    forall s : S,
      generic_consistent E s -> generic_unprovable E s bottom.
Proof.
  intros S F E bottom Hexplosion s Hcon Hbottom.
  apply (generic_consistent_not_inconsistent Hcon).
  intro p.
  exact (@generic_deductive_explosion_provable
    S F E bottom Hexplosion s Hbottom p).
Qed.

(** Source declaration 71/138: syntactic [Complete].  The capability is
    generalized from all connectives to the sole operation it uses. *)
Record generic_syntactically_complete {S F : Type}
    (E : generic_entailment S F) (neg : F -> F) (s : S) : Prop := {
  generic_syntactically_complete_cases :
    forall p, generic_provable E s p \/ generic_provable E s (neg p)
}.

Arguments generic_syntactically_complete_cases
  {S F E neg s} _ _.

(** Source declaration 72/138: [Independent]. *)
Definition generic_independent {S F : Type}
    (E : generic_entailment S F) (neg : F -> F) (s : S) (p : F) : Prop :=
  generic_unprovable E s p /\ generic_unprovable E s (neg p).

(** Source declaration 73/138: [Incomplete]. *)
Record generic_incomplete {S F : Type}
    (E : generic_entailment S F) (neg : F -> F) (s : S) : Prop := {
  generic_incomplete_independent :
    exists p, generic_independent E neg s p
}.

Arguments generic_incomplete_independent
  {S F E neg s} _.

(** Source declaration 74/138: [complete_def]. *)
Lemma generic_syntactically_complete_def :
  forall (S F : Type) (E : generic_entailment S F)
         (neg : F -> F) (s : S),
    generic_syntactically_complete E neg s <->
    forall p, generic_provable E s p \/ generic_provable E s (neg p).
Proof.
  intros S F E neg s; split.
  - exact generic_syntactically_complete_cases.
  - now constructor.
Qed.

(** Source declaration 75/138: [incomplete_def]. *)
Lemma generic_incomplete_def :
  forall (S F : Type) (E : generic_entailment S F)
         (neg : F -> F) (s : S),
    generic_incomplete E neg s <->
    exists p, generic_independent E neg s p.
Proof.
  intros S F E neg s; split.
  - exact generic_incomplete_independent.
  - now constructor.
Qed.

(** Source declaration 76/138: [not_complete_iff_incomplete].  Only
    extraction of the formula at which the universal decision property fails
    is classical. *)
Lemma generic_not_complete_iff_incomplete :
  forall (S F : Type) (E : generic_entailment S F)
         (neg : F -> F) (s : S),
    ~ generic_syntactically_complete E neg s <->
    generic_incomplete E neg s.
Proof.
  intros S F E neg s; split.
  - intro Hnot_complete.
    assert (Hnot_subset :
      ~ (forall p : F, True ->
        generic_provable E s p \/ generic_provable E s (neg p))).
    { intro Hall. apply Hnot_complete. constructor.
      intro p. exact (Hall p I). }
    apply (proj1 (@generic_not_subset_iff_counterexample F
      (fun _ => True)
      (fun p => generic_provable E s p \/
                generic_provable E s (neg p)))) in Hnot_subset.
    destruct Hnot_subset as [p [_ Hneither]]. constructor. exists p.
    split.
    + intro Hp. apply Hneither. now left.
    + intro Hneg. apply Hneither. now right.
  - intros [Hindependent] [Hcases].
    destruct Hindependent as [p [Hnot_p Hnot_neg]].
    destruct (Hcases p) as [Hp | Hneg].
    + exact (Hnot_p Hp).
    + exact (Hnot_neg Hneg).
Qed.

(** Source declaration 77/138: [not_incomplete_iff_complete].  Constructing
    each disjunction from the absence of an independent formula is classical
    double-negation elimination. *)
Lemma generic_not_incomplete_iff_complete :
  forall (S F : Type) (E : generic_entailment S F)
         (neg : F -> F) (s : S),
    ~ generic_incomplete E neg s <->
    generic_syntactically_complete E neg s.
Proof.
  intros S F E neg s; split.
  - intro Hnot_incomplete. constructor. intro p.
    apply NNPP. intro Hneither.
    apply Hnot_incomplete. constructor. exists p. split.
    + intro Hp. apply Hneither. now left.
    + intro Hneg. apply Hneither. now right.
  - intros [Hcases] [Hindependent].
    destruct Hindependent as [p [Hnot_p Hnot_neg]].
    destruct (Hcases p) as [Hp | Hneg].
    + exact (Hnot_p Hp).
    + exact (Hnot_neg Hneg).
Qed.

(** Source declaration 78/138: [consistent_of_incomplete].  The explicit
    independent witness gives consistency directly, so this result does not
    inherit declaration 58's classical counterexample extraction. *)
Lemma generic_consistent_of_incomplete :
  forall (S F : Type) (E : generic_entailment S F)
         (neg : F -> F) (s : S),
    generic_incomplete E neg s -> generic_consistent E s.
Proof.
  intros S F E neg s [Hindependent].
  destruct Hindependent as [p [Hnot_p _]].
  exact (@generic_consistent_of_unprovable S F E s p Hnot_p).
Qed.

(** * Axiomatized entailments and strong cut *)

(** Source declaration 79/138: [Axiomatized].  Inclusion is supplied by the
    adjunctive-context interface rather than stored as a second primitive
    relation. *)
Record generic_axiomatized {S F : Type}
    (E : generic_entailment S F)
    (A : generic_adjunctive_set F S) : Type := {
  generic_axiomatized_raw_axioms :
    forall s : S,
      generic_proof_set E s (generic_adjunctive_carrier A s);
  generic_axiomatized_raw_weakening :
    forall s t : S,
      generic_adjunctive_subset A s t ->
      forall p : F,
        generic_proof E s p -> generic_proof E t p
}.

Arguments generic_axiomatized_raw_axioms
  {S F E A} _ _ _ _.
Arguments generic_axiomatized_raw_weakening
  {S F E A} _ _ _ _ _ _.

(** Source declaration 80/138: alias [wk]. *)
Definition generic_axiomatized_weaken_raw
    {S F : Type} {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (Haxiom : generic_axiomatized E A)
    {s t : S} (Hsub : generic_adjunctive_subset A s t)
    {p : F} (b : generic_proof E s p) : generic_proof E t p :=
  generic_axiomatized_raw_weakening Haxiom s t Hsub p b.

(** Source declaration 81/138: [StrongCut].  Like the source, this preserves
    heterogeneous source and target context types while also making both
    entailment structures explicit. *)
Record generic_strong_cut {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (AT : generic_adjunctive_set F T) : Type := {
  generic_strong_cut_raw :
    forall (s : S) (t : T) (p : F),
      generic_proof_set ES s (generic_adjunctive_carrier AT t) ->
      generic_proof ET t p ->
      generic_proof ES s p
}.

Arguments generic_strong_cut_raw
  {S T F ES ET AT} _ _ _ _ _ _.

(** Source declaration 82/138: [Axiomatized.byAxm]. *)
Definition generic_axiomatized_by_axiom_raw
    {S F : Type} {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (Haxiom : generic_axiomatized E A)
    {s : S} {p : F} (Hp : generic_adjunctive_member A p s) :
    generic_proof E s p :=
  generic_axiomatized_raw_axioms Haxiom s p Hp.

(** Source declaration 83/138: [Axiomatized.by_axm]. *)
Lemma generic_axiomatized_by_axiom :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall (s : S) (p : F),
      generic_adjunctive_member A p s -> generic_provable E s p.
Proof.
  intros S F E A Haxiom s p Hp. constructor.
  exact (generic_axiomatized_by_axiom_raw Haxiom Hp).
Qed.

(** Source declaration 84/138: [Axiomatized.provable_refl]. *)
Lemma generic_axiomatized_provable_refl :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall s : S,
      generic_provable_set E s (generic_adjunctive_carrier A s).
Proof.
  intros S F E A Haxiom s p Hp.
  exact (@generic_axiomatized_by_axiom S F E A Haxiom s p Hp).
Qed.

(** Source declaration 85/138: [Axiomatized.axm_subset]. *)
Lemma generic_axiomatized_axioms_subset_theory :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall (s : S) (p : F),
      generic_adjunctive_carrier A s p ->
      generic_entailment_theory E s p.
Proof.
  intros S F E A Haxiom s.
  exact (@generic_axiomatized_provable_refl S F E A Haxiom s).
Qed.

(** Source declaration 86/138: protected [Axiomatized.adjoin]. *)
Definition generic_axiomatized_adjoin_raw
    {S F : Type} {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (Haxiom : generic_axiomatized E A)
    (p : F) (s : S) :
    generic_proof E (generic_adjunctive_adjoin A p s) p :=
  generic_axiomatized_by_axiom_raw Haxiom
    (@generic_adjunctive_mem_adjoin_self F S A s p).

(** Source declaration 87/138: [Axiomatized.adjoin!]. *)
Lemma generic_axiomatized_adjoin :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall (p : F) (s : S),
      generic_provable E (generic_adjunctive_adjoin A p s) p.
Proof.
  intros S F E A Haxiom p s. constructor.
  exact (generic_axiomatized_adjoin_raw Haxiom p s).
Qed.

(** Source declaration 88/138: [Axiomatized.le_of_subset]. *)
Lemma generic_axiomatized_weaker_of_subset :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall s t : S,
      generic_adjunctive_subset A s t ->
      generic_weaker_than E E s t.
Proof.
  intros S F E A Haxiom s t Hsub. constructor.
  intros p [b]. constructor.
  exact (generic_axiomatized_weaken_raw Haxiom Hsub b).
Qed.

(** Source declaration 89/138: [Axiomatized.weakening!]. *)
Lemma generic_axiomatized_weaken :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall s t : S,
      generic_adjunctive_subset A s t ->
      forall p : F,
        generic_provable E s p -> generic_provable E t p.
Proof.
  intros S F E A Haxiom s t Hsub p [b]. constructor.
  exact (generic_axiomatized_weaken_raw Haxiom Hsub b).
Qed.

(** Source declaration 90/138: [Axiomatized.weakerThanOfSubset]. *)
Definition generic_axiomatized_weaker_of_subset_alias :=
  @generic_axiomatized_weaker_of_subset.

(** Source declaration 91/138: [Axiomatized.toAdjoin]. *)
Definition generic_axiomatized_to_adjoin_raw
    {S F : Type} {E : generic_entailment S F}
    {A : generic_adjunctive_set F S}
    (Haxiom : generic_axiomatized E A)
    (added : F) {s : S} {p : F}
    (b : generic_proof E s p) :
    generic_proof E (generic_adjunctive_adjoin A added s) p :=
  generic_axiomatized_weaken_raw Haxiom
    (@generic_adjunctive_subset_adjoin F S A s added) b.

(** Source declaration 92/138: [Axiomatized.to_adjoin]. *)
Lemma generic_axiomatized_to_adjoin :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall (added : F) (s : S) (p : F),
      generic_provable E s p ->
      generic_provable E (generic_adjunctive_adjoin A added s) p.
Proof.
  intros S F E A Haxiom added s p [b]. constructor.
  exact (generic_axiomatized_to_adjoin_raw Haxiom added b).
Qed.

(** Source declaration 93/138: alias [byAxm]. *)
Definition generic_by_axiom_raw := @generic_axiomatized_by_axiom_raw.

(** Source declaration 94/138: alias [by_axm]. *)
Definition generic_by_axiom := @generic_axiomatized_by_axiom.

(** Source declaration 95/138: alias [wk!]. *)
Definition generic_axiomatized_weaken_alias := @generic_axiomatized_weaken.

(** Source declaration 96/138: [FiniteAxiomatizable]. *)
Definition generic_finitely_axiomatizable
    {S F : Type} (E : generic_entailment S F)
    (A : generic_adjunctive_set F S) (s : S) : Prop :=
  exists finite_context : S,
    generic_adjunctive_finite A finite_context /\
    generic_entailment_equiv E E finite_context s.

(** Source declaration 97/138: [Consistent.of_subset]. *)
Lemma generic_consistent_of_context_subset :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall s t : S,
      generic_consistent E s ->
      generic_adjunctive_subset A t s ->
      generic_consistent E t.
Proof.
  intros S F E A Haxiom s t Hcon Hsub.
  apply (@generic_consistent_of_le S S F E E s t Hcon).
  exact (@generic_axiomatized_weaker_of_subset
    S F E A Haxiom t s Hsub).
Qed.

(** Source declaration 98/138: [Inconsistent.of_supset]. *)
Lemma generic_inconsistent_of_context_superset :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_axiomatized E A ->
    forall s t : S,
      generic_inconsistent E s ->
      generic_adjunctive_subset A s t ->
      generic_inconsistent E t.
Proof.
  intros S F E A Haxiom s t Hinc Hsub.
  apply (@generic_inconsistent_of_ge S S F E E s t Hinc).
  exact (@generic_axiomatized_weaker_of_subset
    S F E A Haxiom s t Hsub).
Qed.

(** Source declaration 99/138: [StrongCut.cut!].  Converting pointwise
    inhabitation into one dependent raw-proof family is exactly declaration
    11's functional-choice boundary; informative description is unnecessary. *)
Lemma generic_strong_cut_provable :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (AT : generic_adjunctive_set F T),
    generic_strong_cut ES ET AT ->
    forall (s : S) (t : T) (p : F),
      generic_provable_set ES s (generic_adjunctive_carrier AT t) ->
      generic_provable ET t p ->
      generic_provable ES s p.
Proof.
  intros S T F ES ET AT Hcut s t p Haxioms [b].
  destruct (proj1
    (@generic_provable_set_iff_inhabited S F ES s
      (generic_adjunctive_carrier AT t)) Haxioms) as [B].
  constructor. exact (generic_strong_cut_raw Hcut s t p B b).
Qed.

(** Source declaration 100/138: [WeakerThan.ofAxm!].  The source uses one
    context type; orienting heterogeneous strong cut exposes the more general
    theorem for distinct context representations and entailments. *)
Lemma generic_weaker_than_of_axioms :
  forall (S T F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (AS : generic_adjunctive_set F S),
    generic_strong_cut ET ES AS ->
    forall (s : S) (t : T),
      generic_provable_set ET t (generic_adjunctive_carrier AS s) ->
      generic_weaker_than ES ET s t.
Proof.
  intros S T F ES ET AS Hcut s t Haxioms. constructor.
  intros p Hp.
  exact (@generic_strong_cut_provable T S F ET ES AS
    Hcut t s p Haxioms Hp).
Qed.

(** Source declaration 101/138: [WeakerThan.ofSubset]. *)
Definition generic_weaker_than_of_context_subset :=
  @generic_axiomatized_weaker_of_subset.

(** * Compactness and deduction *)

(** Source declaration 102/138: [Compact].  The core is chosen from a raw
    proof, so the capability remains informative and lives in [Type]. *)
Record generic_compact_entailment {S F : Type}
    (E : generic_entailment S F)
    (A : generic_adjunctive_set F S) : Type := {
  generic_compact_core :
    forall (s : S) (p : F), generic_proof E s p -> S;
  generic_compact_core_proof :
    forall (s : S) (p : F) (b : generic_proof E s p),
      generic_proof E (generic_compact_core (s := s) (p := p) b) p;
  generic_compact_core_subset :
    forall (s : S) (p : F) (b : generic_proof E s p),
      generic_adjunctive_subset A
        (generic_compact_core (s := s) (p := p) b) s;
  generic_compact_core_finite :
    forall (s : S) (p : F) (b : generic_proof E s p),
      generic_adjunctive_finite A
        (generic_compact_core (s := s) (p := p) b)
}.

Arguments generic_compact_core
  {S F E A} _ _ _ _.
Arguments generic_compact_core_proof
  {S F E A} _ _ _ _.
Arguments generic_compact_core_subset
  {S F E A} _ _ _ _.
Arguments generic_compact_core_finite
  {S F E A} _ _ _ _.

(** Source declaration 103/138: [Compact.finite_provable]. *)
Lemma generic_compact_finite_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S),
    generic_compact_entailment E A ->
    forall (s : S) (p : F),
      generic_provable E s p ->
      exists finite_context : S,
        generic_adjunctive_subset A finite_context s /\
        generic_adjunctive_finite A finite_context /\
        generic_provable E finite_context p.
Proof.
  intros S F E A Hcompact s p [b].
  exists (@generic_compact_core S F E A Hcompact s p b).
  split.
  - exact (@generic_compact_core_subset S F E A Hcompact s p b).
  - split.
    + exact (@generic_compact_core_finite S F E A Hcompact s p b).
    + constructor.
      exact (@generic_compact_core_proof S F E A Hcompact s p b).
Qed.

(** Source declaration 104/138: [inconsistent_compact]. *)
Lemma generic_inconsistent_compact :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S) (bottom : F),
    generic_deductive_explosion E bottom ->
    generic_axiomatized E A ->
    generic_compact_entailment E A ->
    forall s : S,
      generic_inconsistent E s <->
      exists finite_context : S,
        generic_adjunctive_subset A finite_context s /\
        generic_adjunctive_finite A finite_context /\
        generic_inconsistent E finite_context.
Proof.
  intros S F E A bottom Hexplosion Haxiom Hcompact s; split.
  - intro Hinc.
    destruct (@generic_compact_finite_provable
      S F E A Hcompact s bottom (Hinc bottom))
      as [finite_context [Hsub [Hfinite Hbottom]]].
    exists finite_context. split; [exact Hsub |].
    split; [exact Hfinite |].
    exact (@generic_inconsistent_of_provable_bottom
      S F E bottom Hexplosion finite_context Hbottom).
  - intros [finite_context [Hsub [_ Hinc]]].
    exact (@generic_inconsistent_of_context_superset
      S F E A Haxiom finite_context s Hinc Hsub).
Qed.

(** Source declaration 105/138: [consistent_compact].  Both directions have
    direct constructive proofs; no classical negation normalization is
    needed. *)
Lemma generic_consistent_compact :
  forall (S F : Type) (E : generic_entailment S F)
         (A : generic_adjunctive_set F S) (bottom : F),
    generic_deductive_explosion E bottom ->
    generic_axiomatized E A ->
    generic_compact_entailment E A ->
    forall s : S,
      generic_consistent E s <->
      forall finite_context : S,
        generic_adjunctive_subset A finite_context s ->
        generic_adjunctive_finite A finite_context ->
        generic_consistent E finite_context.
Proof.
  intros S F E A bottom Hexplosion Haxiom Hcompact s; split.
  - intros Hcon finite_context Hsub _.
    exact (@generic_consistent_of_context_subset
      S F E A Haxiom s finite_context Hcon Hsub).
  - intro Hall. constructor. intro Hinc.
    destruct (proj1 (@generic_inconsistent_compact
      S F E A bottom Hexplosion Haxiom Hcompact s) Hinc)
      as [finite_context [Hsub [Hfinite Hinc_finite]]].
    exact (generic_consistent_not_inconsistent
      (Hall finite_context Hsub Hfinite) Hinc_finite).
Qed.

(** Source declaration 106/138: [Deduction].  Only implication and context
    extension are used, so both operations are explicit instead of requiring
    full connective or adjunctive-context packages. *)
Record generic_deduction {S F : Type}
    (E : generic_entailment S F)
    (imp : F -> F -> F) (adjoin : F -> S -> S) : Type := {
  generic_deduction_forward_raw :
    forall (s : S) (p q : F),
      generic_proof E (adjoin p s) q ->
      generic_proof E s (imp p q);
  generic_deduction_inverse_raw :
    forall (s : S) (p q : F),
      generic_proof E s (imp p q) ->
      generic_proof E (adjoin p s) q
}.

Arguments generic_deduction_forward_raw
  {S F E imp adjoin} _ _ _ _ _.
Arguments generic_deduction_inverse_raw
  {S F E imp adjoin} _ _ _ _ _.

(** Source declaration 107/138: alias [deduction]. *)
Definition generic_deduction_raw := @generic_deduction_forward_raw.

(** Source declaration 108/138: [Deduction.of_insert!]. *)
Lemma generic_deduction_forward :
  forall (S F : Type) (E : generic_entailment S F)
         (imp : F -> F -> F) (adjoin : F -> S -> S),
    generic_deduction E imp adjoin ->
    forall (s : S) (p q : F),
      generic_provable E (adjoin p s) q ->
      generic_provable E s (imp p q).
Proof.
  intros S F E imp adjoin Hdeduction s p q [b]. constructor.
  exact (generic_deduction_forward_raw Hdeduction s p q b).
Qed.

(** Source declaration 109/138: alias [deduction!]. *)
Definition generic_deduction_provable := @generic_deduction_forward.

(** Source declaration 110/138: [Deduction.inv!]. *)
Lemma generic_deduction_inverse :
  forall (S F : Type) (E : generic_entailment S F)
         (imp : F -> F -> F) (adjoin : F -> S -> S),
    generic_deduction E imp adjoin ->
    forall (s : S) (p q : F),
      generic_provable E s (imp p q) ->
      generic_provable E (adjoin p s) q.
Proof.
  intros S F E imp adjoin Hdeduction s p q [b]. constructor.
  exact (generic_deduction_inverse_raw Hdeduction s p q b).
Qed.

(** Source declaration 111/138: [deduction_iff]. *)
Lemma generic_deduction_iff :
  forall (S F : Type) (E : generic_entailment S F)
         (imp : F -> F -> F) (adjoin : F -> S -> S),
    generic_deduction E imp adjoin ->
    forall (s : S) (p q : F),
      generic_provable E (adjoin p s) q <->
      generic_provable E s (imp p q).
Proof.
  intros S F E imp adjoin Hdeduction s p q; split.
  - exact (@generic_deduction_forward
      S F E imp adjoin Hdeduction s p q).
  - exact (@generic_deduction_inverse
      S F E imp adjoin Hdeduction s p q).
Qed.

(** * Soundness and semantic completeness *)

(** Source declaration 112/138: [Sound]. *)
Record generic_sound {S M F : Type}
    (E : generic_entailment S F) (V : generic_semantics M F)
    (s : S) (m : M) : Prop := {
  generic_sound_provable :
    forall p : F,
      generic_provable E s p -> generic_models V m p
}.

(** Source declaration 113/138: semantic [Complete]. *)
Record generic_complete {S M F : Type}
    (E : generic_entailment S F) (V : generic_semantics M F)
    (s : S) (m : M) : Prop := {
  generic_complete_models :
    forall p : F,
      generic_models V m p -> generic_provable E s p
}.

Arguments generic_sound_provable
  {S M F E V s m} _ _ _.
Arguments generic_complete_models
  {S M F E V s m} _ _ _.

(** Source declaration 114/138: [Sound.not_provable_of_countermodel]. *)
Lemma generic_sound_unprovable_of_countermodel :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (m : M),
    generic_sound E V s m ->
    forall p : F,
      generic_not_models V m p -> generic_unprovable E s p.
Proof.
  intros S M F E V s m Hsound p Hcounter Hprovable.
  exact (Hcounter (generic_sound_provable Hsound p Hprovable)).
Qed.

(** Source declaration 115/138: [Sound.consistent_of_meaningful]. *)
Lemma generic_sound_consistent_of_meaningful :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (m : M),
    generic_sound E V s m ->
    generic_meaningful V m -> generic_consistent E s.
Proof.
  intros S M F E V s m Hsound [Hcounter].
  destruct Hcounter as [p Hnot_models].
  exact (@generic_consistent_of_unprovable S F E s p
    (@generic_sound_unprovable_of_countermodel
      S M F E V s m Hsound p Hnot_models)).
Qed.

(** Source declaration 116/138: [Sound.consistent_of_model].  Only a bottom
    formula and its semantic falsity law are required. *)
Lemma generic_sound_consistent_of_bottom_model :
  forall (S M F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (V : generic_semantics M F),
    generic_semantics_bottom C V ->
    forall (s : S) (m : M),
      generic_sound E V s m -> generic_consistent E s.
Proof.
  intros S M F E C V Hbottom s m Hsound.
  exact (@generic_sound_consistent_of_meaningful
    S M F E V s m Hsound
    (@generic_meaningful_of_bottom M F C V Hbottom m)).
Qed.

(** Source declaration 117/138: [Sound.modelsSet_of_prfSet].  Despite the
    source name, its premise is pointwise inhabited provability. *)
Lemma generic_sound_models_set_of_provable_set :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (m : M),
    generic_sound E V s m ->
    forall T : F -> Prop,
      generic_provable_set E s T -> generic_models_set V m T.
Proof.
  intros S M F E V s m Hsound T Hprovable. constructor.
  intros p Hp. exact (generic_sound_provable Hsound p (Hprovable p Hp)).
Qed.

(** Source declaration 118/138: [Sound.consequence_of_provable]. *)
Lemma generic_sound_consequence_of_provable :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    generic_sound E (generic_set_semantics V)
      s (generic_model_set V T) ->
    forall p : F,
      generic_provable E s p -> generic_consequence V T p.
Proof.
  intros S M F E V s T Hsound p Hprovable.
  exact (generic_sound_provable Hsound p Hprovable).
Qed.

(** Source declaration 119/138: [Sound.consistent_of_satisfiable].  A direct
    witness proof uses only the forward satisfiability direction and avoids
    the classical set-meaningfulness equivalence. *)
Lemma generic_sound_consistent_of_satisfiable :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    (forall m : M, generic_meaningful V m) ->
    generic_sound E (generic_set_semantics V)
      s (generic_model_set V T) ->
    generic_satisfiable V T -> generic_consistent E s.
Proof.
  intros S M F E V s T Hall_meaningful Hsound [m Hmodels].
  constructor. intro Hinc.
  destruct (Hall_meaningful m) as [Hcounter].
  destruct Hcounter as [p Hnot_models]. apply Hnot_models.
  pose proof (generic_sound_provable Hsound p (Hinc p)) as Hset_models.
  exact (Hset_models m Hmodels).
Qed.

(** Source declaration 120/138:
    [Complete.exists_countermodel_of_not_provable].  The direct implication
    is constructive; contraposition normalization is unnecessary. *)
Lemma generic_complete_countermodel_of_unprovable :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (m : M),
    generic_complete E V s m ->
    forall p : F,
      generic_unprovable E s p -> generic_not_models V m p.
Proof.
  intros S M F E V s m Hcomplete p Hunprovable Hmodels.
  exact (Hunprovable (generic_complete_models Hcomplete p Hmodels)).
Qed.

(** Source declaration 121/138: [Complete.meaningful_of_consistent].  A
    countermodel formula must be extracted from consistency, which is the
    exact excluded-middle boundary already isolated at declaration 58. *)
Lemma generic_complete_meaningful_of_consistent :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (m : M),
    generic_complete E V s m ->
    generic_consistent E s -> generic_meaningful V m.
Proof.
  intros S M F E V s m Hcomplete Hconsistent.
  destruct (generic_consistent_exists_unprovable Hconsistent)
    as [p Hunprovable].
  constructor. exists p.
  exact (@generic_complete_countermodel_of_unprovable
    S M F E V s m Hcomplete p Hunprovable).
Qed.

(** Source declaration 122/138: [Complete.provable_of_consequence]. *)
Lemma generic_complete_provable_of_consequence :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    generic_complete E (generic_set_semantics V)
      s (generic_model_set V T) ->
    forall p : F,
      generic_consequence V T p -> generic_provable E s p.
Proof.
  intros S M F E V s T Hcomplete p Hconsequence.
  exact (generic_complete_models Hcomplete p Hconsequence).
Qed.

(** Source declaration 123/138: [Complete.provable_iff_consequence]. *)
Lemma generic_complete_provable_iff_consequence :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    generic_complete E (generic_set_semantics V)
      s (generic_model_set V T) ->
    generic_sound E (generic_set_semantics V)
      s (generic_model_set V T) ->
    forall p : F,
      generic_consequence V T p <-> generic_provable E s p.
Proof.
  intros S M F E V s T Hcomplete Hsound p; split.
  - exact (@generic_complete_provable_of_consequence
      S M F E V s T Hcomplete p).
  - exact (@generic_sound_consequence_of_provable
      S M F E V s T Hsound p).
Qed.

(** Source declaration 124/138: [Complete.satisfiable_of_consistent]. *)
Lemma generic_complete_satisfiable_of_consistent :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    (forall m : M, generic_meaningful V m) ->
    generic_complete E (generic_set_semantics V)
      s (generic_model_set V T) ->
    generic_consistent E s -> generic_satisfiable V T.
Proof.
  intros S M F E V s T Hall_meaningful Hcomplete Hconsistent.
  apply (proj2 (@generic_meaningful_iff_satisfiable M F V
    Hall_meaningful T)).
  exact (@generic_complete_meaningful_of_consistent
    S (M -> Prop) F E (generic_set_semantics V)
    s (generic_model_set V T) Hcomplete Hconsistent).
Qed.

(** Source declaration 125/138: [Complete.inconsistent_of_unsatisfiable].
    Unsatisfiability makes every consequence vacuous, yielding inconsistency
    constructively and without the source section's unused connective and
    meaningfulness hypotheses. *)
Lemma generic_complete_inconsistent_of_unsatisfiable :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    generic_complete E (generic_set_semantics V)
      s (generic_model_set V T) ->
    ~ generic_satisfiable V T -> generic_inconsistent E s.
Proof.
  intros S M F E V s T Hcomplete Hunsatisfiable p.
  apply (generic_complete_models Hcomplete p).
  intros m Hmodels. exfalso. apply Hunsatisfiable.
  now exists m.
Qed.

(** Source declaration 126/138: [Complete.consistent_iff_satisfiable]. *)
Lemma generic_complete_consistent_iff_satisfiable :
  forall (S M F : Type) (E : generic_entailment S F)
         (V : generic_semantics M F) (s : S) (T : F -> Prop),
    (forall m : M, generic_meaningful V m) ->
    generic_complete E (generic_set_semantics V)
      s (generic_model_set V T) ->
    generic_sound E (generic_set_semantics V)
      s (generic_model_set V T) ->
    generic_consistent E s <-> generic_satisfiable V T.
Proof.
  intros S M F E V s T Hall_meaningful Hcomplete Hsound; split.
  - exact (@generic_complete_satisfiable_of_consistent
      S M F E V s T Hall_meaningful Hcomplete).
  - exact (@generic_sound_consistent_of_satisfiable
      S M F E V s T Hall_meaningful Hsound).
Qed.

(** Source declaration 127/138: [Complete.weakerthan_of_models].  Making the
    two entailment structures and context types independent strengthens the
    source theorem without changing its semantic inclusion direction. *)
Lemma generic_complete_weaker_than_of_models :
  forall (S T M F : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (V : generic_semantics M F)
         (s : S) (t : T) (source_theory target_theory : F -> Prop),
    generic_complete ES (generic_set_semantics V)
      s (generic_model_set V source_theory) ->
    generic_sound ET (generic_set_semantics V)
      t (generic_model_set V target_theory) ->
    (forall m : M,
      generic_models_set V m source_theory ->
      generic_models_set V m target_theory) ->
    generic_weaker_than ET ES t s.
Proof.
  intros S T M F ES ET V s t source_theory target_theory
    Hcomplete Hsound Hmodels. constructor.
  intros p Hprovable.
  apply (generic_complete_models Hcomplete p).
  intros m Hsource.
  pose proof (generic_sound_provable Hsound p Hprovable) as Htarget_models.
  exact (Htarget_models m (Hmodels m Hsource)).
Qed.

(** * Entailment pullback *)

(** Source declaration 128/138: [Entailment.Pullback]. *)
Record generic_pullback (S : Type) {F G : Type} (f : G -> F) : Type := {
  generic_pullback_base : S
}.

Arguments generic_pullback_base {S F G f} _.

(** Source declaration 129/138: [Entailment.pullback]. *)
Definition generic_pullback_of {S F G : Type}
    (s : S) (f : G -> F) : generic_pullback S f :=
  {| generic_pullback_base := s |}.

(** Source declaration 130/138: the pullback [Entailment] instance. *)
Definition generic_pullback_entailment
    {S F G : Type} (E : generic_entailment S F) (f : G -> F) :
    generic_entailment (generic_pullback S f) G :=
  {| generic_proof :=
       fun s p => generic_proof E (generic_pullback_base s) (f p) |}.

(** Source declaration 131/138: [Pullback.pullback_forget]. *)
Lemma generic_pullback_forget :
  forall (S F G : Type) (s : S) (f : G -> F),
    generic_pullback_base (generic_pullback_of s f) = s.
Proof. reflexivity. Qed.

(** Source declaration 132/138: [Pullback.provable_iff]. *)
Lemma generic_pullback_provable_iff :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F) (p : G),
    generic_provable (generic_pullback_entailment E f)
      (generic_pullback_of s f) p <->
    generic_provable E s (f p).
Proof. reflexivity. Qed.

(** Source declaration 133/138: [Pullback.unprovable_iff]. *)
Lemma generic_pullback_unprovable_iff :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F) (p : G),
    generic_unprovable (generic_pullback_entailment E f)
      (generic_pullback_of s f) p <->
    generic_unprovable E s (f p).
Proof. reflexivity. Qed.

(** Source declaration 134/138: [Pullback.provableSet_iff]. *)
Lemma generic_pullback_provable_set_iff :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F) (T : G -> Prop),
    generic_provable_set (generic_pullback_entailment E f)
      (generic_pullback_of s f) T <->
    generic_provable_set E s
      (fun q : F => exists p : G, T p /\ f p = q).
Proof.
  intros S F G E s f T; split.
  - intros H q [p [Hp Heq]]. destruct Heq. exact (H p Hp).
  - intros H p Hp. apply (H (f p)). exists p. now split.
Qed.

(** Source declaration 135/138: [Pullback.theory_eq].  Here the source's
    literal predicate equality is definitional, so it is retained without
    functional or propositional extensionality. *)
Lemma generic_pullback_theory_eq :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F),
    generic_entailment_theory (generic_pullback_entailment E f)
      (generic_pullback_of s f) =
    (fun p : G => generic_entailment_theory E s (f p)).
Proof. reflexivity. Qed.

(** Source declaration 136/138: [Pullback.weakerThan].  The context and
    entailment types may differ, strengthening the source's homogeneous
    presentation. *)
Lemma generic_pullback_weaker_than :
  forall (S T F G : Type)
         (ES : generic_entailment S F) (ET : generic_entailment T F)
         (s : S) (t : T) (f : G -> F),
    generic_weaker_than ES ET s t ->
    generic_weaker_than
      (generic_pullback_entailment ES f)
      (generic_pullback_entailment ET f)
      (generic_pullback_of s f) (generic_pullback_of t f).
Proof.
  intros S T F G ES ET s t f Hweak. constructor.
  intros p Hp. exact (generic_weaker_subset Hweak (f p) Hp).
Qed.

(** Source declaration 137/138: [Pullback.inconsistent]. *)
Lemma generic_pullback_inconsistent :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F),
    generic_inconsistent E s ->
    generic_inconsistent (generic_pullback_entailment E f)
      (generic_pullback_of s f).
Proof.
  intros S F G E s f Hinc p. exact (Hinc (f p)).
Qed.

(** Source declaration 138/138: [Pullback.consistent]. *)
Lemma generic_pullback_consistent :
  forall (S F G : Type) (E : generic_entailment S F)
         (s : S) (f : G -> F),
    generic_consistent (generic_pullback_entailment E f)
      (generic_pullback_of s f) ->
    generic_consistent E s.
Proof.
  intros S F G E s f Hconsistent. constructor. intro Hinc.
  apply (generic_consistent_not_inconsistent Hconsistent).
  exact (@generic_pullback_inconsistent S F G E s f Hinc).
Qed.
