(** Abstract provability, incompleteness, and Löb principles.

    Foundation states this layer for quoted first-order sentences.  None of
    its proofs inspect terms or formulas: they use only classical
    propositional reasoning, a provability operator, and diagonalization.
    We therefore state the port over arbitrary modal-formula atoms and an
    arbitrary formula endomorphism.  This both relaxes the source hypotheses
    and makes the reusable mathematical core independent of Gödel coding. *)

From FoundationModal Require Import Syntax LogicInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Small factored helpers for applying one, two, or three already-proved
    premises to a classical tautology. *)
Lemma pa_tautology1 : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q,
  classical_tautology (Imp p q) -> L p -> L q.
Proof.
  intros A L Hclass p q Htaut Hp.
  eapply logic_modus_ponens; [exact Hclass | | exact Hp].
  now apply logic_classical_tautology.
Qed.

Lemma pa_tautology2 : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q r,
  classical_tautology (Imp p (Imp q r)) -> L p -> L q -> L r.
Proof.
  intros A L Hclass p q r Htaut Hp Hq.
  eapply logic_modus_ponens; [exact Hclass | | exact Hq].
  eapply logic_modus_ponens; [exact Hclass | | exact Hp].
  now apply logic_classical_tautology.
Qed.

Lemma pa_tautology3 : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q r s,
  classical_tautology (Imp p (Imp q (Imp r s))) ->
  L p -> L q -> L r -> L s.
Proof.
  intros A L Hclass p q r s Htaut Hp Hq Hr.
  eapply logic_modus_ponens; [exact Hclass | | exact Hr].
  eapply logic_modus_ponens; [exact Hclass | | exact Hq].
  eapply logic_modus_ponens; [exact Hclass | | exact Hp].
  now apply logic_classical_tautology.
Qed.

Lemma pa_iff_left : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q, L (Iff p q) -> L (Imp p q).
Proof.
  intros A L Hclass p q Hiff.
  eapply pa_tautology1; [exact Hclass | | exact Hiff].
  intro rho. unfold Iff, And, Neg. simpl. tauto.
Qed.

Lemma pa_iff_right : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q, L (Iff p q) -> L (Imp q p).
Proof.
  intros A L Hclass p q Hiff.
  eapply pa_tautology1; [exact Hclass | | exact Hiff].
  intro rho. unfold Iff, And, Neg. simpl. tauto.
Qed.

Lemma pa_iff_intro : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q,
  L (Imp p q) -> L (Imp q p) -> L (Iff p q).
Proof.
  intros A L Hclass p q Hpq Hqp. unfold Iff.
  now apply logic_and_intro.
Qed.

Lemma pa_iff_trans : forall (A : Type) (L : modal_logic_set A),
  classical_logic L -> forall p q r,
  L (Iff p q) -> L (Iff q r) -> L (Iff p r).
Proof.
  intros A L Hclass p q r Hpq Hqr.
  eapply (@pa_iff_intro A L Hclass p r).
  - exact (logic_imp_trans Hclass
      (pa_iff_left Hclass Hpq) (pa_iff_left Hclass Hqr)).
  - exact (logic_imp_trans Hclass
      (pa_iff_right Hclass Hqr) (pa_iff_right Hclass Hpq)).
Qed.

(** Source structures [Provability], [HBL2], [HBL3], [Mono], [Ext],
    [Rosser], [FormalizedCompleteOn], [Kreisel], and [SoundOn]. *)
Record pa_provability {A : Type}
    (L0 L : modal_logic_set A) : Type := {
  pa_box : formula A -> formula A;
  pa_D1_raw : forall p, L p -> L0 (pa_box p)
}.

Arguments pa_box {A L0 L} _ _.
Arguments pa_D1_raw {A L0 L} _ _ _.

Definition pa_con {A L0 L} (B : pa_provability L0 L) : formula A :=
  Neg (pa_box B Bottom).

Definition pa_dia {A L0 L} (B : pa_provability L0 L)
    (p : formula A) : formula A :=
  Neg (pa_box B (Neg p)).

Lemma pa_D1 : forall (A : Type) (L0 L : modal_logic_set A)
    (B : pa_provability L0 L) p,
  L p -> L0 (pa_box B p).
Proof. intros; now apply pa_D1_raw. Qed.

Record pa_hbl2 {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_D2 : forall p q,
    L0 (Imp (pa_box B (Imp p q))
      (Imp (pa_box B p) (pa_box B q)))
}.

Record pa_hbl3 {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_D3 : forall p, L0 (Imp (pa_box B p) (pa_box B (pa_box B p)))
}.

Record pa_hbl {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_hbl_D2 : pa_hbl2 B;
  pa_hbl_D3 : pa_hbl3 B
}.

Record pa_mono {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_monotone : forall p q, L (Imp p q) ->
    L0 (Imp (pa_box B p) (pa_box B q))
}.

Record pa_ext {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_extensional : forall p q, L (Iff p q) ->
    L0 (Iff (pa_box B p) (pa_box B q))
}.

Record pa_rosser {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_Ros : forall p, L (Neg p) -> L0 (Neg (pa_box B p))
}.

Record pa_formalized_complete_on {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) (p : formula A) : Prop := {
  pa_formalized_complete : L0 (Imp p (pa_box B p))
}.

Record pa_kreisel {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : Prop := {
  pa_KR : forall p, L (pa_box B p) -> L p
}.

Record pa_sound_on {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L)
    (truth : formula A -> Prop) : Prop := {
  pa_sound : forall p, truth (pa_box B p) -> L p
}.

(** Any interpretation sound for [L0] turns semantic soundness of the
    provability operator into the source's syntactical soundness principle. *)
Lemma pa_syntactical_sound : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L)
    (truth : formula A -> Prop),
  pa_sound_on B truth ->
  (forall p, L0 p -> truth p) ->
  forall p, L0 (pa_box B p) -> L p.
Proof.
  intros A L0 L B truth Hsound Hmodel p Hp.
  apply (pa_sound Hsound). now apply Hmodel.
Qed.

Lemma pa_hbl3_of_formalized_complete : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L),
  (forall p, pa_formalized_complete_on B (pa_box B p)) ->
  pa_hbl3 B.
Proof.
  intros A L0 L B Hall. constructor. intro p.
  exact (pa_formalized_complete (Hall p)).
Qed.

(** D2 already entails the source's monotonicity and extensionality
    interfaces, so downstream proofs do not repeat their derivation. *)
Lemma pa_mono_of_hbl2 : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass0 : classical_logic L0)
    (B : pa_provability L0 L),
  pa_hbl2 B -> pa_mono B.
Proof.
  intros A L0 L Hclass0 B H2. constructor. intros p q Hpq.
  eapply logic_modus_ponens; [exact Hclass0 | |].
  - exact (pa_D2 H2 p q).
  - exact (pa_D1 B Hpq).
Qed.

Lemma pa_ext_of_hbl2 : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_hbl2 B -> pa_ext B.
Proof.
  intros A L0 L Hclass0 Hclass B H2. constructor. intros p q Hiff.
  eapply (@pa_iff_intro A L0 Hclass0 (pa_box B p) (pa_box B q)).
  - apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)).
    now apply pa_iff_left.
  - apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)).
    now apply pa_iff_right.
Qed.

Lemma pa_bew_distribute_imply : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass0 : classical_logic L0)
    (B : pa_provability L0 L),
  pa_hbl2 B -> forall p q,
  L0 (pa_box B (Imp p q)) ->
  L0 (Imp (pa_box B p) (pa_box B q)).
Proof.
  intros A L0 L Hclass0 B H2 p q Hboxed.
  eapply logic_modus_ponens; [exact Hclass0 | | exact Hboxed].
  exact (pa_D2 H2 p q).
Qed.

Lemma pa_bew_distribute_and : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_hbl2 B -> forall p q,
  L0 (Imp (pa_box B (And p q))
    (And (pa_box B p) (pa_box B q))).
Proof.
  intros A L0 L Hclass0 Hclass B H2 p q.
  apply (logic_imp_and_intro Hclass0).
  - apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)).
    apply (logic_classical_tautology Hclass).
    intro rho. unfold And, Neg. simpl. tauto.
  - apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)).
    apply (logic_classical_tautology Hclass).
    intro rho. unfold And, Neg. simpl. tauto.
Qed.

Lemma pa_bew_distribute_and_provable : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_hbl2 B -> forall p q,
  L0 (pa_box B (And p q)) ->
  L0 (And (pa_box B p) (pa_box B q)).
Proof.
  intros A L0 L Hclass0 Hclass B H2 p q Hboxed.
  eapply logic_modus_ponens; [exact Hclass0 | | exact Hboxed].
  exact (pa_bew_distribute_and Hclass0 Hclass H2 p q).
Qed.

Lemma pa_bew_collect_and : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_hbl2 B -> forall p q,
  L0 (Imp (And (pa_box B p) (pa_box B q))
    (pa_box B (And p q))).
Proof.
  intros A L0 L Hclass0 Hclass B H2 p q.
  pose proof (pa_mono_of_hbl2 Hclass0 H2) as Hmono.
  assert (Hp : L0 (Imp (pa_box B p)
      (pa_box B (Imp q (And p q))))).
  { apply (pa_monotone Hmono).
    apply (logic_classical_tautology Hclass).
    intro rho. unfold And, Neg. simpl. tauto. }
  assert (Hmp : L0 (Imp (pa_box B (Imp q (And p q)))
      (Imp (pa_box B q) (pa_box B (And p q))))).
  { exact (pa_D2 H2 q (And p q)). }
  eapply pa_tautology2; [exact Hclass0 | | exact Hp | exact Hmp].
  intro rho. unfold And, Neg. simpl. tauto.
Qed.

Lemma pa_dia_mono : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_mono B -> forall p q,
  L (Imp p q) -> L0 (Imp (pa_dia B p) (pa_dia B q)).
Proof.
  intros A L0 L Hclass0 Hclass B Hmono p q Hpq.
  assert (Hcontra : L (Imp (Neg q) (Neg p))).
  { eapply pa_tautology1; [exact Hclass | | exact Hpq].
    intro rho. unfold Neg. simpl. tauto. }
  pose proof (pa_monotone Hmono Hcontra) as Hbox.
  eapply pa_tautology1; [exact Hclass0 | | exact Hbox].
  intro rho. unfold pa_dia, Neg. simpl. tauto.
Qed.

Lemma pa_mono_weaker : forall (A : Type)
    (L0 L : modal_logic_set A) (Hweak : logic_subset L0 L)
    (B : pa_provability L0 L),
  pa_mono B -> forall p q,
  L0 (Imp p q) -> L0 (Imp (pa_box B p) (pa_box B q)).
Proof.
  intros A L0 L Hweak B Hmono p q Hpq.
  apply (pa_monotone Hmono), Hweak. exact Hpq.
Qed.

Lemma pa_ext_weaker : forall (A : Type)
    (L0 L : modal_logic_set A) (Hweak : logic_subset L0 L)
    (B : pa_provability L0 L),
  pa_ext B -> forall p q,
  L0 (Iff p q) -> L0 (Iff (pa_box B p) (pa_box B q)).
Proof.
  intros A L0 L Hweak B Hext p q Hpq.
  apply (pa_extensional Hext), Hweak. exact Hpq.
Qed.

(** Diagonalization is generalized from substitution into a quoted
    semisentence to a fixed point for any formula endomorphism. *)
Record pa_diagonalization {A : Type}
    (L0 : modal_logic_set A) : Type := {
  pa_fixedpoint : (formula A -> formula A) -> formula A;
  pa_diagonal : forall theta,
    L0 (Iff (pa_fixedpoint theta) (theta (pa_fixedpoint theta)))
}.

Arguments pa_fixedpoint {A L0} _ _.
Arguments pa_diagonal {A L0} _ _.

Definition pa_godel {A L0 L} (D : pa_diagonalization L0)
    (B : pa_provability L0 L) : formula A :=
  pa_fixedpoint D (fun p => Neg (pa_box B p)).

Lemma pa_godel_spec : forall (A : Type) (L0 L : modal_logic_set A)
    (D : pa_diagonalization L0) (B : pa_provability L0 L),
  L0 (Iff (pa_godel D B) (Neg (pa_box B (pa_godel D B)))).
Proof.
  intros A L0 L D B. unfold pa_godel.
  exact (pa_diagonal D (fun p => Neg (pa_box B p))).
Qed.

Definition pa_independent {A} (L : modal_logic_set A)
    (p : formula A) : Prop := ~ L p /\ ~ L (Neg p).

Definition pa_incomplete {A} (L : modal_logic_set A) : Prop :=
  exists p, pa_independent L p.

Theorem pa_unprovable_godel : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  logic_consistent L -> ~ L (pa_godel D B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B Hconsistent HG.
  pose proof (pa_D1 B HG) as HBG0.
  pose proof (Hweak _ HBG0) as HBG.
  pose proof (Hweak _ (pa_godel_spec D B)) as Hspec.
  pose proof (pa_iff_left Hclass Hspec) as HGneg.
  pose proof (logic_modus_ponens Hclass HGneg HG) as HnegBG.
  exact (logic_not_neg_of Hclass Hconsistent HBG HnegBG).
Qed.

Theorem pa_unrefutable_godel : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_kreisel B -> logic_consistent L -> ~ L (Neg (pa_godel D B)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HK Hconsistent HnegG.
  pose proof (Hweak _ (pa_godel_spec D B)) as Hspec.
  assert (HBG : L (pa_box B (pa_godel D B))).
  { eapply pa_tautology2; [exact Hclass | | exact Hspec | exact HnegG].
    intro rho. unfold Iff, And, Neg. simpl. tauto. }
  pose proof (pa_KR HK HBG) as HG.
  exact (logic_not_neg_of Hclass Hconsistent HG HnegG).
Qed.

Theorem pa_godel_independent : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_kreisel B -> logic_consistent L ->
  pa_independent L (pa_godel D B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HK Hconsistent. split.
  - exact (@pa_unprovable_godel A L0 L Hclass0 Hclass
      Hweak D B Hconsistent).
  - exact (@pa_unrefutable_godel A L0 L Hclass0 Hclass
      Hweak D B HK Hconsistent).
Qed.

Theorem pa_first_incompleteness : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_kreisel B -> logic_consistent L -> pa_incomplete L.
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HK Hconsistent.
  exists (pa_godel D B).
  exact (@pa_godel_independent A L0 L Hclass0 Hclass
    Hweak D B HK Hconsistent).
Qed.

(** * Formalized consistency and the second incompleteness theorem *)

Lemma pa_formalized_consistent_of_unprovable : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_hbl2 B -> forall sigma,
  L0 (Imp (Neg (pa_box B sigma)) (pa_con B)).
Proof.
  intros A L0 L Hclass0 Hclass B H2 sigma.
  assert (Hefq : L (Imp Bottom sigma)).
  { apply (logic_classical_tautology Hclass).
    intro rho. simpl. tauto. }
  pose proof (pa_bew_distribute_imply Hclass0 H2
    (pa_D1 B Hefq)) as Hmono.
  eapply pa_tautology1; [exact Hclass0 | | exact Hmono].
  intro rho. unfold pa_con, Neg. simpl. tauto.
Qed.

Theorem pa_formalized_unprovable_godel : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B ->
  L0 (Imp (pa_con B) (Neg (pa_box B (pa_godel D B)))).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH.
  pose proof (pa_hbl_D2 HH) as H2.
  pose proof (pa_hbl_D3 HH) as H3.
  set (G := pa_godel D B).
  assert (HBG_BBG : L0 (Imp (pa_box B G)
      (pa_box B (pa_box B G)))).
  { exact (pa_D3 H3 G). }
  assert (HG_imp : L (Imp G (Imp (pa_box B G) Bottom))).
  { apply Hweak. apply pa_iff_left; [exact Hclass0 |].
    unfold G. apply pa_godel_spec. }
  assert (HBG_Bimp : L0 (Imp (pa_box B G)
      (pa_box B (Imp (pa_box B G) Bottom)))).
  { apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)). exact HG_imp. }
  pose proof (pa_D2 H2 (pa_box B G) Bottom) as Hinternal_mp.
  eapply pa_tautology3;
    [exact Hclass0 | | exact HBG_BBG | exact HBG_Bimp |
      exact Hinternal_mp].
  intro rho. unfold pa_con, Neg. simpl. tauto.
Qed.

Theorem pa_godel_iff_con : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> L0 (Iff (pa_godel D B) (pa_con B)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH.
  pose proof (pa_hbl_D2 HH) as H2.
  assert (Hforward : L0 (Imp (Neg (pa_box B (pa_godel D B)))
      (pa_con B))).
  { apply pa_formalized_consistent_of_unprovable;
      [exact Hclass0 | exact Hclass | exact H2]. }
  assert (Hbackward : L0 (Imp (pa_con B)
      (Neg (pa_box B (pa_godel D B))))).
  { exact (pa_formalized_unprovable_godel
      Hclass0 Hclass Hweak D HH). }
  exact (pa_iff_trans Hclass0 (pa_godel_spec D B)
    (pa_iff_intro Hclass0 Hforward Hbackward)).
Qed.

Theorem pa_con_unprovable : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> logic_consistent L -> ~ L (pa_con B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH Hconsistent Hcon.
  pose proof (Hweak _ (pa_godel_iff_con Hclass0 Hclass Hweak D HH))
    as Hiff.
  pose proof (pa_iff_right Hclass Hiff) as HconG.
  pose proof (logic_modus_ponens Hclass HconG Hcon) as HG.
  exact (@pa_unprovable_godel A L0 L Hclass0 Hclass Hweak
    D B Hconsistent HG).
Qed.

Theorem pa_con_unrefutable : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> pa_kreisel B -> logic_consistent L ->
  ~ L (Neg (pa_con B)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH HK Hconsistent Hnegcon.
  pose proof (Hweak _ (pa_godel_iff_con Hclass0 Hclass Hweak D HH))
    as Hiff.
  assert (HnegG : L (Neg (pa_godel D B))).
  { eapply pa_tautology2; [exact Hclass | | exact Hiff | exact Hnegcon].
    intro rho. unfold Iff, And, Neg. simpl. tauto. }
  exact (@pa_unrefutable_godel A L0 L Hclass0 Hclass Hweak
    D B HK Hconsistent HnegG).
Qed.

Theorem pa_con_independent : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> pa_kreisel B -> logic_consistent L ->
  pa_independent L (pa_con B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH HK Hconsistent. split.
  - exact (pa_con_unprovable Hclass0 Hclass Hweak D HH Hconsistent).
  - exact (pa_con_unrefutable Hclass0 Hclass Hweak D HH HK Hconsistent).
Qed.

(** * Löb's theorem *)

Definition pa_kreisel_sentence {A L0 L}
    (D : pa_diagonalization L0) (B : pa_provability L0 L)
    (sigma : formula A) : formula A :=
  pa_fixedpoint D (fun p => Imp (pa_box B p) sigma).

Lemma pa_kreisel_spec : forall (A : Type) (L0 L : modal_logic_set A)
    (D : pa_diagonalization L0) (B : pa_provability L0 L) sigma,
  L0 (Iff (pa_kreisel_sentence D B sigma)
    (Imp (pa_box B (pa_kreisel_sentence D B sigma)) sigma)).
Proof.
  intros A L0 L D B sigma. unfold pa_kreisel_sentence.
  exact (pa_diagonal D (fun p => Imp (pa_box B p) sigma)).
Qed.

Lemma pa_kreisel_box_mono : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> forall sigma,
  L0 (Imp (pa_box B (pa_kreisel_sentence D B sigma))
    (pa_box B sigma)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH sigma.
  pose proof (pa_hbl_D2 HH) as H2.
  pose proof (pa_hbl_D3 HH) as H3.
  set (K := pa_kreisel_sentence D B sigma).
  assert (HKstep : L (Imp K (Imp (pa_box B K) sigma))).
  { apply Hweak. apply pa_iff_left; [exact Hclass0 |].
    unfold K. apply pa_kreisel_spec. }
  assert (HBK_nested : L0 (Imp (pa_box B K)
      (pa_box B (Imp (pa_box B K) sigma)))).
  { apply (pa_monotone (pa_mono_of_hbl2 Hclass0 H2)). exact HKstep. }
  pose proof (pa_D3 H3 K) as HBK_BBK.
  pose proof (pa_D2 H2 (pa_box B K) sigma) as Hinternal_mp.
  eapply pa_tautology3;
    [exact Hclass0 | | exact HBK_nested | exact HBK_BBK |
      exact Hinternal_mp].
  intro rho. simpl. tauto.
Qed.

Theorem pa_lob_theorem : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> forall sigma,
  L (Imp (pa_box B sigma) sigma) -> L sigma.
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH sigma Hreflection.
  set (K := pa_kreisel_sentence D B sigma).
  pose proof (Hweak _ (pa_kreisel_box_mono
    Hclass0 Hclass Hweak D HH sigma)) as HBK_Bsigma.
  pose proof (logic_imp_trans Hclass HBK_Bsigma Hreflection) as HBK_sigma.
  pose proof (Hweak _ (pa_kreisel_spec D B sigma)) as Hspec.
  pose proof (pa_iff_right Hclass Hspec) as Hstep_K.
  pose proof (logic_modus_ponens Hclass Hstep_K HBK_sigma) as HK.
  pose proof (Hweak _ (pa_D1 B HK)) as HBK.
  exact (logic_modus_ponens Hclass HBK_sigma HBK).
Qed.

Theorem pa_formalized_lob_theorem : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> forall sigma,
  L0 (Imp (pa_box B (Imp (pa_box B sigma) sigma))
    (pa_box B sigma)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH sigma.
  pose proof (pa_hbl_D2 HH) as H2.
  set (K := pa_kreisel_sentence D B sigma).
  pose proof (pa_kreisel_box_mono Hclass0 Hclass Hweak D HH sigma)
    as HBK_Bsigma.
  assert (Href_Kstep : L0 (Imp (Imp (pa_box B sigma) sigma)
      (Imp (pa_box B K) sigma))).
  { eapply pa_tautology1; [exact Hclass0 | | exact HBK_Bsigma].
    intro rho. simpl. tauto. }
  pose proof (pa_iff_right Hclass0 (pa_kreisel_spec D B sigma))
    as HKstep_K.
  pose proof (logic_imp_trans Hclass0 Href_Kstep HKstep_K)
    as Href_K.
  pose proof (pa_D1 B (Hweak _ Href_K)) as HB_refK.
  pose proof (pa_D2 H2 (Imp (pa_box B sigma) sigma) K) as HD2ref.
  pose proof (logic_modus_ponens Hclass0 HD2ref HB_refK)
    as HBref_BK.
  exact (logic_imp_trans Hclass0 HBref_BK HBK_Bsigma).
Qed.

Theorem pa_formalized_unprovable_not_con : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> pa_kreisel B -> logic_consistent L ->
  ~ L (Imp (pa_con B) (Neg (pa_box B (Neg (pa_con B))))).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH HK Hconsistent Hformal.
  assert (Href : L (Imp (pa_box B (Neg (pa_con B)))
      (Neg (pa_con B)))).
  { eapply pa_tautology1; [exact Hclass | | exact Hformal].
    intro rho. unfold pa_con, Neg. simpl. tauto. }
  pose proof (pa_lob_theorem Hclass0 Hclass Hweak D HH Href) as Hnegcon.
  exact (pa_con_unrefutable Hclass0 Hclass Hweak D HH HK
    Hconsistent Hnegcon).
Qed.

Theorem pa_formalized_unrefutable_godel : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_hbl B -> pa_kreisel B -> logic_consistent L ->
  ~ L (Imp (pa_con B)
    (Neg (pa_box B (Neg (pa_godel D B))))).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HH HK Hconsistent Hformal.
  pose proof (pa_hbl_D2 HH) as H2.
  pose proof (Hweak _ (pa_godel_iff_con Hclass0 Hclass Hweak D HH))
    as HGcon.
  assert (Hneg_equiv : L (Iff (Neg (pa_godel D B)) (Neg (pa_con B)))).
  { eapply pa_tautology1; [exact Hclass | | exact HGcon].
    intro rho. unfold Iff, And, Neg. simpl. tauto. }
  pose proof (pa_extensional (pa_ext_of_hbl2 Hclass0 Hclass H2)
    Hneg_equiv) as Hbox_equiv0.
  pose proof (Hweak _ Hbox_equiv0) as Hbox_equiv.
  assert (Hforbidden : L (Imp (pa_con B)
      (Neg (pa_box B (Neg (pa_con B)))))).
  { eapply pa_tautology2;
      [exact Hclass | | exact Hformal | exact Hbox_equiv].
    intro rho. unfold Iff, And, Neg. simpl. tauto. }
  exact (pa_formalized_unprovable_not_con Hclass0 Hclass Hweak D
    HH HK Hconsistent Hforbidden).
Qed.

(** * Rosser provability *)

Theorem pa_unrefutable_rosser : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_rosser B -> logic_consistent L ->
  ~ L (Neg (pa_godel D B)).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HR Hconsistent HnegG.
  pose proof (Hweak _ (pa_Ros HR HnegG)) as HnegBG.
  pose proof (Hweak _ (pa_godel_spec D B)) as Hspec.
  pose proof (pa_iff_right Hclass Hspec) as HnegBG_G.
  pose proof (logic_modus_ponens Hclass HnegBG_G HnegBG) as HG.
  exact (logic_not_neg_of Hclass Hconsistent HG HnegG).
Qed.

Theorem pa_rosser_independent : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_rosser B -> logic_consistent L ->
  pa_independent L (pa_godel D B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HR Hconsistent. split.
  - exact (@pa_unprovable_godel A L0 L Hclass0 Hclass Hweak
      D B Hconsistent).
  - exact (@pa_unrefutable_rosser A L0 L Hclass0 Hclass Hweak
      D B HR Hconsistent).
Qed.

Theorem pa_rosser_first_incompleteness : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (D : pa_diagonalization L0)
    (B : pa_provability L0 L),
  pa_rosser B -> logic_consistent L -> pa_incomplete L.
Proof.
  intros A L0 L Hclass0 Hclass Hweak D B HR Hconsistent.
  exists (pa_godel D B).
  exact (@pa_rosser_independent A L0 L Hclass0 Hclass Hweak
    D B HR Hconsistent).
Qed.

Theorem pa_kreisel_remark : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (B : pa_provability L0 L),
  pa_rosser B -> L (pa_con B).
Proof.
  intros A L0 L Hclass0 Hclass Hweak B HR.
  assert (Hnotbot : L (Neg Bottom)).
  { apply (logic_classical_tautology Hclass).
    intro rho. unfold Neg. simpl. tauto. }
  exact (Hweak _ (pa_Ros HR Hnotbot)).
Qed.
