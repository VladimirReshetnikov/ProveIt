(**
  Four equivalent presentations of Gödel--Löb logic.

  This module ports the mathematical theorem surfaces of the pinned files

    - [Modal/Entailment/K4Loeb.lean],
    - [Modal/Entailment/K4Henkin.lean],
    - [Modal/Entailment/K4Hen.lean], and
    - [Modal/Hilbert/GL_K4Loeb_K4Henkin_K4Hen.lean].

  Foundation proves the Loeb axiom inside the Loeb-rule calculus by a
  finite-context derivation.  Here the same auxiliary K4 theorem is obtained
  more directly: every transitive frame validates [box (L p) -> L p], so the
  already checked K4 completeness theorem supplies the derivation.  The rest
  of the equivalence is purely syntactic.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke NormalHilbert LogicInfrastructure CanonicalExtensions
  GLGrzDerivations KHenIncompleteness QuasiNormalS.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The K4 base as a predicate-valued normal logic *)

Definition alternative_K4_normal_logic : normal_logic (@K4_proves nat) :=
  @normal_proves_logic_is_normal schema_Four
    schema_Four_substitution_closed.

Definition alternative_K4_classical_logic : classical_logic (@K4_proves nat) :=
  quasi_classical (normal_quasi alternative_K4_normal_logic).

(** * K4 with the Loeb rule *)

Inductive K4Loeb_proves : formula nat -> Prop :=
| K4Loeb_base : forall p, K4_proves p -> K4Loeb_proves p
| K4Loeb_mp : forall p q,
    K4Loeb_proves (Imp p q) -> K4Loeb_proves p -> K4Loeb_proves q
| K4Loeb_nec : forall p,
    K4Loeb_proves p -> K4Loeb_proves (Box p)
| K4Loeb_loeb : forall p,
    K4Loeb_proves (Imp (Box p) p) -> K4Loeb_proves p.

Arguments K4Loeb_base {p} _.
Arguments K4Loeb_mp {p q} _ _.
Arguments K4Loeb_nec {p} _.
Arguments K4Loeb_loeb {p} _.

Theorem K4Loeb_proves_substitute :
  forall (sigma : nat -> formula nat) p,
    K4Loeb_proves p -> K4Loeb_proves (substitute sigma p).
Proof.
  intros sigma p Hp; induction Hp; simpl.
  - apply K4Loeb_base.
    exact (@normal_proves_substitute schema_Four
      schema_Four_substitution_closed nat nat sigma p H).
  - eapply K4Loeb_mp; eauto.
  - now apply K4Loeb_nec.
  - now apply K4Loeb_loeb.
Qed.

Definition K4Loeb_classical_logic : classical_logic K4Loeb_proves.
Proof.
  constructor.
  - intros p Hp. apply K4Loeb_base.
    now apply (logic_classical_tautology alternative_K4_classical_logic).
  - intros p q. apply K4Loeb_mp.
Defined.

Definition K4Loeb_normal_logic : normal_logic K4Loeb_proves.
Proof.
  constructor.
  - constructor.
    + exact K4Loeb_classical_logic.
    + intros p q. apply K4Loeb_base.
      exact (quasi_modal_K (normal_quasi alternative_K4_normal_logic) p q).
    + intro p. apply K4Loeb_base.
      exact (quasi_dia_duality
        (normal_quasi alternative_K4_normal_logic) p).
    + exact K4Loeb_proves_substitute.
  - intros p. apply K4Loeb_nec.
Defined.

(** * K4 with the Henkin rule *)

Inductive K4Henkin_proves : formula nat -> Prop :=
| K4Henkin_base : forall p, K4_proves p -> K4Henkin_proves p
| K4Henkin_mp : forall p q,
    K4Henkin_proves (Imp p q) -> K4Henkin_proves p -> K4Henkin_proves q
| K4Henkin_nec : forall p,
    K4Henkin_proves p -> K4Henkin_proves (Box p)
| K4Henkin_henkin : forall p,
    K4Henkin_proves (Iff (Box p) p) -> K4Henkin_proves p.

Arguments K4Henkin_base {p} _.
Arguments K4Henkin_mp {p q} _ _.
Arguments K4Henkin_nec {p} _.
Arguments K4Henkin_henkin {p} _.

Theorem K4Henkin_proves_substitute :
  forall (sigma : nat -> formula nat) p,
    K4Henkin_proves p -> K4Henkin_proves (substitute sigma p).
Proof.
  intros sigma p Hp; induction Hp; simpl.
  - apply K4Henkin_base.
    exact (@normal_proves_substitute schema_Four
      schema_Four_substitution_closed nat nat sigma p H).
  - eapply K4Henkin_mp; eauto.
  - now apply K4Henkin_nec.
  - now apply K4Henkin_henkin.
Qed.

Definition K4Henkin_classical_logic : classical_logic K4Henkin_proves.
Proof.
  constructor.
  - intros p Hp. apply K4Henkin_base.
    now apply (logic_classical_tautology alternative_K4_classical_logic).
  - intros p q. apply K4Henkin_mp.
Defined.

Definition K4Henkin_normal_logic : normal_logic K4Henkin_proves.
Proof.
  constructor.
  - constructor.
    + exact K4Henkin_classical_logic.
    + intros p q. apply K4Henkin_base.
      exact (quasi_modal_K (normal_quasi alternative_K4_normal_logic) p q).
    + intro p. apply K4Henkin_base.
      exact (quasi_dia_duality
        (normal_quasi alternative_K4_normal_logic) p).
    + exact K4Henkin_proves_substitute.
  - intros p. apply K4Henkin_nec.
Defined.

(** * Normal K4 plus the Henkin axiom *)

Definition K4Hen_schema : modal_axiom_schema :=
  schema_union schema_Four schema_Hen.

Definition K4Hen_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves K4Hen_schema AtomType.

Lemma K4Hen_schema_substitution_closed :
  schema_substitution_closed K4Hen_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_Four_substitution_closed.
  - exact schema_Hen_substitution_closed.
Qed.

Definition K4Hen_normal_logic : normal_logic (@K4Hen_proves nat) :=
  @normal_proves_logic_is_normal K4Hen_schema
    K4Hen_schema_substitution_closed.

Definition K4Hen_classical_logic : classical_logic (@K4Hen_proves nat) :=
  quasi_classical (normal_quasi K4Hen_normal_logic).

Lemma K4_weaker_than_K4Hen :
  forall (AtomType : Type) (p : formula AtomType),
    K4_proves p -> K4Hen_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. now left.
Qed.

Lemma K4Hen_proves_Four :
  forall (AtomType : Type) (p : formula AtomType), K4Hen_proves (Four p).
Proof. intros AtomType p. apply Np_extra. left. now exists p. Qed.

Lemma K4Hen_proves_Hen :
  forall (AtomType : Type) (p : formula AtomType), K4Hen_proves (Hen p).
Proof. intros AtomType p. apply Np_extra. right. now exists p. Qed.

(** * The three derived rules *)

(** The one K4 fact needed to turn the Loeb rule into the Loeb axiom. *)
Theorem K4_proves_box_L_implies_L :
  forall p : formula nat, K4_proves (Imp (Box (L p)) (L p)).
Proof.
  intro p. apply K4_complete.
  intros F Htrans V w HboxL Hboxprem y Rwy.
  apply (Hboxprem y Rwy).
  apply (HboxL y Rwy).
  intros z Ryz.
  apply Hboxprem.
  exact (Htrans w y z Rwy Ryz).
Qed.

Theorem K4Loeb_proves_L :
  forall p, K4Loeb_proves (L p).
Proof.
  intro p. apply K4Loeb_loeb, K4Loeb_base.
  exact (K4_proves_box_L_implies_L p).
Qed.

(** Foundation's K4Henkin instance: Four turns a one-way fixed point into a
    boxed fixed point, so the Henkin rule yields the Loeb rule. *)
Theorem K4Henkin_loeb_rule :
  forall p,
    K4Henkin_proves (Imp (Box p) p) -> K4Henkin_proves p.
Proof.
  intros p Hdrop.
  assert (Hforward : K4Henkin_proves (Imp (Box (Box p)) (Box p))).
  {
    eapply K4Henkin_mp.
    - apply K4Henkin_base, Np_modal_K.
    - now apply K4Henkin_nec.
  }
  assert (Hback : K4Henkin_proves (Imp (Box p) (Box (Box p)))).
  { apply K4Henkin_base, Np_extra. now exists p. }
  assert (Hfixed : K4Henkin_proves (Iff (Box (Box p)) (Box p))).
  {
    unfold Iff.
    exact (logic_and_intro K4Henkin_classical_logic Hforward Hback).
  }
  exact (K4Henkin_mp Hdrop (K4Henkin_henkin Hfixed)).
Qed.

Theorem K4Henkin_proves_L :
  forall p, K4Henkin_proves (L p).
Proof.
  intro p. apply K4Henkin_loeb_rule, K4Henkin_base.
  exact (K4_proves_box_L_implies_L p).
Qed.

(** Foundation's K4Hen instance: the boxed Henkin axiom turns a proved fixed
    point into its boxed half, and its other half then yields the formula. *)
Theorem K4Hen_henkin_rule :
  forall p : formula nat,
    K4Hen_proves (Iff (Box p) p) -> K4Hen_proves p.
Proof.
  intros p Hfixed.
  assert (Hbox : K4Hen_proves (Box p)).
  {
    exact (Np_mp (K4Hen_proves_Hen p) (Np_nec Hfixed)).
  }
  assert (Hdrop : K4Hen_proves (Imp (Box p) p)).
  {
    eapply Np_mp; [| exact Hfixed].
    apply (logic_classical_tautology K4Hen_classical_logic).
    intro rho. unfold Iff, And, Neg; simpl; tauto.
  }
  exact (Np_mp Hdrop Hbox).
Qed.

Theorem K4Hen_loeb_rule :
  forall p : formula nat,
    K4Hen_proves (Imp (Box p) p) -> K4Hen_proves p.
Proof.
  intros p Hdrop.
  assert (Hforward : K4Hen_proves (Imp (Box (Box p)) (Box p))).
  {
    eapply Np_mp.
    - apply Np_modal_K.
    - now apply Np_nec.
  }
  assert (Hback : K4Hen_proves (Imp (Box p) (Box (Box p)))).
  { exact (K4Hen_proves_Four p). }
  assert (Hfixed : K4Hen_proves (Iff (Box (Box p)) (Box p))).
  {
    unfold Iff.
    exact (logic_and_intro K4Hen_classical_logic Hforward Hback).
  }
  exact (Np_mp Hdrop (K4Hen_henkin_rule Hfixed)).
Qed.

Theorem K4Hen_proves_L :
  forall p : formula nat, K4Hen_proves (L p).
Proof.
  intro p. apply K4Hen_loeb_rule, K4_weaker_than_K4Hen.
  exact (K4_proves_box_L_implies_L p).
Qed.

(** * Equivalence with GL *)

Lemma K4_weaker_than_GL :
  forall p : formula nat, K4_proves p -> GL_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [q ->]. exact (GL_proves_Four q).
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Lemma GL_loeb_rule :
  forall p : formula nat, GL_proves (Imp (Box p) p) -> GL_proves p.
Proof.
  intros p Hdrop.
  exact (Np_mp Hdrop (Np_mp (GL_proves_L p) (Np_nec Hdrop))).
Qed.

Lemma GL_henkin_rule :
  forall p : formula nat, GL_proves (Iff (Box p) p) -> GL_proves p.
Proof.
  intros p Hfixed.
  assert (Hbox : GL_proves (Box p)).
  {
    exact (Np_mp (GL_proves_Hen p) (Np_nec Hfixed)).
  }
  assert (Hdrop : GL_proves (Imp (Box p) p)).
  {
    eapply Np_mp; [| exact Hfixed].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Iff, And, Neg; simpl; tauto.
  }
  exact (Np_mp Hdrop Hbox).
Qed.

Theorem GL_weaker_than_K4Loeb :
  forall p, GL_proves p -> K4Loeb_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply K4Loeb_base, Np_imply_K.
  - apply K4Loeb_base, Np_imply_S.
  - apply K4Loeb_base, Np_elim_contra.
  - apply K4Loeb_base, Np_modal_K.
  - destruct H as [q ->]. exact (K4Loeb_proves_L q).
  - eapply K4Loeb_mp; eauto.
  - now apply K4Loeb_nec.
Qed.

Theorem K4Loeb_weaker_than_GL :
  forall p, K4Loeb_proves p -> GL_proves p.
Proof.
  intros p Hp; induction Hp.
  - now apply K4_weaker_than_GL.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
  - now apply GL_loeb_rule.
Qed.

Theorem GL_weaker_than_K4Henkin :
  forall p, GL_proves p -> K4Henkin_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply K4Henkin_base, Np_imply_K.
  - apply K4Henkin_base, Np_imply_S.
  - apply K4Henkin_base, Np_elim_contra.
  - apply K4Henkin_base, Np_modal_K.
  - destruct H as [q ->]. exact (K4Henkin_proves_L q).
  - eapply K4Henkin_mp; eauto.
  - now apply K4Henkin_nec.
Qed.

Theorem K4Henkin_weaker_than_GL :
  forall p, K4Henkin_proves p -> GL_proves p.
Proof.
  intros p Hp; induction Hp.
  - now apply K4_weaker_than_GL.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
  - now apply GL_henkin_rule.
Qed.

Theorem GL_weaker_than_K4Hen :
  forall p : formula nat, GL_proves p -> K4Hen_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [q ->]. exact (K4Hen_proves_L q).
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Theorem K4Hen_weaker_than_GL :
  forall p : formula nat, K4Hen_proves p -> GL_proves p.
Proof.
  intros p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [Hfour | Hhen].
    + destruct Hfour as [q ->]. exact (GL_proves_Four q).
    + destruct Hhen as [q ->]. exact (GL_proves_Hen q).
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Theorem provable_GL_K4Loeb_iff :
  forall p, GL_proves p <-> K4Loeb_proves p.
Proof. split; [apply GL_weaker_than_K4Loeb | apply K4Loeb_weaker_than_GL]. Qed.

Theorem provable_GL_K4Henkin_iff :
  forall p, GL_proves p <-> K4Henkin_proves p.
Proof. split; [apply GL_weaker_than_K4Henkin | apply K4Henkin_weaker_than_GL]. Qed.

Theorem provable_GL_K4Hen_iff :
  forall p : formula nat, GL_proves p <-> K4Hen_proves p.
Proof. split; [apply GL_weaker_than_K4Hen | apply K4Hen_weaker_than_GL]. Qed.

(** Source-facing four-way equivalence. *)
Theorem provable_GL_TFAE :
  forall p : formula nat,
    (GL_proves p <-> K4Loeb_proves p) /\
    (GL_proves p <-> K4Henkin_proves p) /\
    (GL_proves p <-> K4Hen_proves p).
Proof.
  intro p; repeat split; intro H.
  - now apply GL_weaker_than_K4Loeb.
  - now apply K4Loeb_weaker_than_GL.
  - now apply GL_weaker_than_K4Henkin.
  - now apply K4Henkin_weaker_than_GL.
  - now apply GL_weaker_than_K4Hen.
  - now apply K4Hen_weaker_than_GL.
Qed.

Theorem GL_equiv_K4Loeb : logic_equiv GL_proves K4Loeb_proves.
Proof.
  split; intros p Hp.
  - now apply GL_weaker_than_K4Loeb.
  - now apply K4Loeb_weaker_than_GL.
Qed.

Theorem GL_equiv_K4Henkin : logic_equiv GL_proves K4Henkin_proves.
Proof.
  split; intros p Hp.
  - now apply GL_weaker_than_K4Henkin.
  - now apply K4Henkin_weaker_than_GL.
Qed.

Theorem GL_equiv_K4Hen :
  logic_equiv (@GL_proves nat) (@K4Hen_proves nat).
Proof.
  split; intros p Hp.
  - now apply GL_weaker_than_K4Hen.
  - now apply K4Hen_weaker_than_GL.
Qed.

(** The strict K4 predecessor used by Foundation's maximal-unprovability
    layer. *)
Theorem K4_unprovable_atomic_L :
  ~ K4_proves (L (Atom 0)).
Proof.
  intro HK4.
  pose proof (K4_proves_sound_on_transitive_frame
    reflexive_singleton_transitive HK4) as Hvalid.
  specialize (Hvalid (fun _ _ => False) tt).
  unfold L, Loeb in Hvalid. simpl in Hvalid.
  assert (Hante :
    unit -> True -> (unit -> True -> False) -> False).
  {
    intros [] _ Hbox. apply (Hbox tt). constructor.
  }
  apply (Hvalid Hante tt). constructor.
Qed.

Theorem K4_strictly_weaker_GL :
  normal_strictly_weaker K4_proves GL_proves.
Proof.
  split.
  - exact K4_weaker_than_GL.
  - exists (L (Atom 0)). split.
    + exact (GL_proves_L (Atom 0)).
    + exact K4_unprovable_atomic_L.
Qed.

Theorem not_S4_weakerThan_GL :
  ~ (forall p : formula nat, S4_proves p -> GL_proves p).
Proof.
  intro Hinclude. apply GL_unprovable_atomic_T.
  apply Hinclude. apply Np_extra. left.
  now exists (Atom 0).
Qed.
