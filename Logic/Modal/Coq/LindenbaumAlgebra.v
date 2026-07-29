(**
  The Lindenbaum algebra of a classical predicate-valued logic.

  This module is a reusable Coq counterpart of the pinned Foundation module
  [Logic/LindenbaumAlgebra.lean].  Foundation forms a quotient of formulas by
  provable biconditional.  The Boolean-algebra interface in this repository
  already carries an explicit setoid equality, so the carrier remains the
  formula type itself and [lindenbaum_equiv] is its equality relation.  This
  avoids quotient representatives and the source's implementation-only
  [DecidableEq] assumption without changing the mathematics.

  The exported readback lemmas correspond to Foundation's
  [of_eq_of], [le_def], [top_def], [bot_def], [inf_def], [sup_def],
  [himp_def], and [compl_def].  The final metatheorems port
  [provable_iff_eq_top], [inconsistent_iff_trivial],
  [consistent_iff_nontrivial], and [nontrivial_of_consistent], translating
  quotient equality and [Nontrivial] to the explicit relation [ba_equiv].
*)

From FoundationModal Require Import
  Syntax GenericSemantics GenericLogicSymbol LogicInfrastructure
  EntailmentExtensions ModalAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Generic setoid Heyting interfaces *)

(** Foundation uses Mathlib's quotient-based hierarchy.  These records keep
    equality explicit, matching the repository's Boolean algebra style and
    avoiding quotient representatives and equality decision. *)
Record generalized_heyting_algebra (A : Type) := {
  gha_equiv : A -> A -> Prop;
  gha_le : A -> A -> Prop;
  gha_top : A;
  gha_meet : A -> A -> A;
  gha_join : A -> A -> A;
  gha_imp : A -> A -> A;

  gha_equiv_refl : forall a, gha_equiv a a;
  gha_equiv_sym : forall a b, gha_equiv a b -> gha_equiv b a;
  gha_equiv_trans : forall a b c,
    gha_equiv a b -> gha_equiv b c -> gha_equiv a c;
  gha_le_refl : forall a, gha_le a a;
  gha_le_trans : forall a b c, gha_le a b -> gha_le b c -> gha_le a c;
  gha_le_antisymmetric : forall a b,
    gha_le a b -> gha_le b a -> gha_equiv a b;
  gha_le_respects_equiv : forall a a' b b',
    gha_equiv a a' -> gha_equiv b b' ->
    (gha_le a b <-> gha_le a' b');
  gha_meet_respects_equiv : forall a a' b b',
    gha_equiv a a' -> gha_equiv b b' ->
    gha_equiv (gha_meet a b) (gha_meet a' b');
  gha_join_respects_equiv : forall a a' b b',
    gha_equiv a a' -> gha_equiv b b' ->
    gha_equiv (gha_join a b) (gha_join a' b');
  gha_imp_respects_equiv : forall a a' b b',
    gha_equiv a a' -> gha_equiv b b' ->
    gha_equiv (gha_imp a b) (gha_imp a' b');

  gha_meet_le_left : forall a b, gha_le (gha_meet a b) a;
  gha_meet_le_right : forall a b, gha_le (gha_meet a b) b;
  gha_le_meet : forall a b c,
    gha_le a b -> gha_le a c -> gha_le a (gha_meet b c);
  gha_le_join_left : forall a b, gha_le a (gha_join a b);
  gha_le_join_right : forall a b, gha_le b (gha_join a b);
  gha_join_le : forall a b c,
    gha_le a c -> gha_le b c -> gha_le (gha_join a b) c;
  gha_le_top : forall a, gha_le a gha_top;
  gha_imp_adjoint : forall x a b,
    gha_le (gha_meet x a) b <-> gha_le x (gha_imp a b)
}.

Arguments gha_equiv {A} _ _ _.
Arguments gha_le {A} _ _ _.
Arguments gha_top {A} _.
Arguments gha_meet {A} _ _ _.
Arguments gha_join {A} _ _ _.
Arguments gha_imp {A} _ _ _.

Record heyting_algebra (A : Type) := {
  ha_generalized : generalized_heyting_algebra A;
  ha_bottom : A;
  ha_compl : A -> A;
  ha_compl_respects_equiv : forall a b,
    gha_equiv ha_generalized a b ->
    gha_equiv ha_generalized (ha_compl a) (ha_compl b);
  ha_bottom_le : forall a,
    gha_le ha_generalized ha_bottom a;
  ha_imp_bottom : forall a,
    gha_equiv ha_generalized
      (gha_imp ha_generalized a ha_bottom) (ha_compl a)
}.

Arguments ha_bottom {A} _.
Arguments ha_compl {A} _ _.

(** * Abstract minimal Lindenbaum construction *)

Definition generic_lindenbaum_equiv {F : Type}
    (C : generic_connectives F) (Prov : F -> Prop)
    (p q : F) : Prop :=
  Prov (generic_formula_iff C p q).

Definition generic_lindenbaum_le {F : Type}
    (C : generic_connectives F) (Prov : F -> Prop)
    (p q : F) : Prop :=
  Prov (generic_imp C p q).

(** This capability is the precise proof-theoretic surface consumed by the
    generalized-Heyting construction.  It is weaker than any classical logic
    package and permits primitive intuitionistic conjunction/disjunction. *)
Record generic_lindenbaum_minimal_laws {F : Type}
    (C : generic_connectives F) (Prov : F -> Prop) : Prop := {
  glm_equiv_refl : forall p,
    generic_lindenbaum_equiv C Prov p p;
  glm_equiv_sym : forall p q,
    generic_lindenbaum_equiv C Prov p q ->
    generic_lindenbaum_equiv C Prov q p;
  glm_equiv_trans : forall p q r,
    generic_lindenbaum_equiv C Prov p q ->
    generic_lindenbaum_equiv C Prov q r ->
    generic_lindenbaum_equiv C Prov p r;
  glm_le_refl : forall p, generic_lindenbaum_le C Prov p p;
  glm_le_trans : forall p q r,
    generic_lindenbaum_le C Prov p q ->
    generic_lindenbaum_le C Prov q r ->
    generic_lindenbaum_le C Prov p r;
  glm_le_antisymmetric : forall p q,
    generic_lindenbaum_le C Prov p q ->
    generic_lindenbaum_le C Prov q p ->
    generic_lindenbaum_equiv C Prov p q;
  glm_le_respects_equiv : forall p p' q q',
    generic_lindenbaum_equiv C Prov p p' ->
    generic_lindenbaum_equiv C Prov q q' ->
    (generic_lindenbaum_le C Prov p q <->
     generic_lindenbaum_le C Prov p' q');
  glm_and_respects_equiv : forall p p' q q',
    generic_lindenbaum_equiv C Prov p p' ->
    generic_lindenbaum_equiv C Prov q q' ->
    generic_lindenbaum_equiv C Prov
      (generic_and C p q) (generic_and C p' q');
  glm_or_respects_equiv : forall p p' q q',
    generic_lindenbaum_equiv C Prov p p' ->
    generic_lindenbaum_equiv C Prov q q' ->
    generic_lindenbaum_equiv C Prov
      (generic_or C p q) (generic_or C p' q');
  glm_imp_respects_equiv : forall p p' q q',
    generic_lindenbaum_equiv C Prov p p' ->
    generic_lindenbaum_equiv C Prov q q' ->
    generic_lindenbaum_equiv C Prov
      (generic_imp C p q) (generic_imp C p' q');
  glm_and_le_left : forall p q,
    generic_lindenbaum_le C Prov (generic_and C p q) p;
  glm_and_le_right : forall p q,
    generic_lindenbaum_le C Prov (generic_and C p q) q;
  glm_le_and : forall p q r,
    generic_lindenbaum_le C Prov p q ->
    generic_lindenbaum_le C Prov p r ->
    generic_lindenbaum_le C Prov p (generic_and C q r);
  glm_le_or_left : forall p q,
    generic_lindenbaum_le C Prov p (generic_or C p q);
  glm_le_or_right : forall p q,
    generic_lindenbaum_le C Prov q (generic_or C p q);
  glm_or_le : forall p q r,
    generic_lindenbaum_le C Prov p r ->
    generic_lindenbaum_le C Prov q r ->
    generic_lindenbaum_le C Prov (generic_or C p q) r;
  glm_le_top : forall p,
    generic_lindenbaum_le C Prov p (generic_top C);
  glm_imp_adjoint : forall p q r,
    generic_lindenbaum_le C Prov (generic_and C p q) r <->
    generic_lindenbaum_le C Prov p (generic_imp C q r);
  glm_provable_iff_top : forall p,
    Prov p <->
    generic_lindenbaum_equiv C Prov p (generic_top C)
}.

Definition generic_lindenbaum_generalized_heyting
    {F : Type} (C : generic_connectives F) (Prov : F -> Prop)
    (H : generic_lindenbaum_minimal_laws C Prov) :
    generalized_heyting_algebra F.
Proof.
  refine
    {| gha_equiv := generic_lindenbaum_equiv C Prov;
       gha_le := generic_lindenbaum_le C Prov;
       gha_top := generic_top C;
       gha_meet := generic_and C;
       gha_join := generic_or C;
       gha_imp := generic_imp C |}.
  - exact (glm_equiv_refl H).
  - exact (glm_equiv_sym H).
  - exact (glm_equiv_trans H).
  - exact (glm_le_refl H).
  - exact (glm_le_trans H).
  - exact (glm_le_antisymmetric H).
  - exact (glm_le_respects_equiv H).
  - exact (glm_and_respects_equiv H).
  - exact (glm_or_respects_equiv H).
  - exact (glm_imp_respects_equiv H).
  - exact (glm_and_le_left H).
  - exact (glm_and_le_right H).
  - exact (glm_le_and H).
  - exact (glm_le_or_left H).
  - exact (glm_le_or_right H).
  - exact (glm_or_le H).
  - exact (glm_le_top H).
  - exact (glm_imp_adjoint H).
Defined.

Record generic_lindenbaum_intuitionistic_laws {F : Type}
    (C : generic_connectives F) (Prov : F -> Prop) : Prop := {
  gli_minimal : generic_lindenbaum_minimal_laws C Prov;
  gli_neg_respects_equiv : forall p q,
    generic_lindenbaum_equiv C Prov p q ->
    generic_lindenbaum_equiv C Prov
      (generic_neg C p) (generic_neg C q);
  gli_bottom_le : forall p,
    generic_lindenbaum_le C Prov (generic_bottom C) p;
  gli_imp_bottom : forall p,
    generic_lindenbaum_equiv C Prov
      (generic_imp C p (generic_bottom C)) (generic_neg C p)
}.

Definition generic_lindenbaum_heyting
    {F : Type} (C : generic_connectives F) (Prov : F -> Prop)
    (H : generic_lindenbaum_intuitionistic_laws C Prov) :
    heyting_algebra F.
Proof.
  refine
    {| ha_generalized :=
         @generic_lindenbaum_generalized_heyting F C Prov (gli_minimal H);
       ha_bottom := generic_bottom C;
       ha_compl := generic_neg C |}.
  - exact (gli_neg_respects_equiv H).
  - exact (gli_bottom_le H).
  - exact (gli_imp_bottom H).
Defined.

(** Generic beta/readback laws are definitional because formula
    representatives replace quotient representatives. *)
Lemma generic_lindenbaum_equiv_readback :
  forall (F : Type) (C : generic_connectives F) (Prov : F -> Prop)
         (H : generic_lindenbaum_minimal_laws C Prov) p q,
    gha_equiv (@generic_lindenbaum_generalized_heyting F C Prov H) p q <->
    Prov (generic_formula_iff C p q).
Proof. reflexivity. Qed.

Lemma generic_lindenbaum_order_readback :
  forall (F : Type) (C : generic_connectives F) (Prov : F -> Prop)
         (H : generic_lindenbaum_minimal_laws C Prov) p q,
    gha_le (@generic_lindenbaum_generalized_heyting F C Prov H) p q <->
    Prov (generic_imp C p q).
Proof. reflexivity. Qed.

Lemma generic_lindenbaum_provable_iff_top :
  forall (F : Type) (C : generic_connectives F) (Prov : F -> Prop)
         (H : generic_lindenbaum_minimal_laws C Prov) p,
    Prov p <->
    gha_equiv (@generic_lindenbaum_generalized_heyting F C Prov H) p
      (gha_top (@generic_lindenbaum_generalized_heyting F C Prov H)).
Proof. intros F C Prov H p. exact (glm_provable_iff_top H p). Qed.

(** * Provable equivalence and order *)

(** Foundation's [Entailment.ProvablyEquivalent]. *)
Definition lindenbaum_equiv {AtomType : Type}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Iff p q).

(** The implication order underlying Foundation's [LE] instance. *)
Definition lindenbaum_le {AtomType : Type}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Imp p q).

(** Source [ProvablyEquivalent.refl]. *)
Lemma lindenbaum_equiv_refl :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, lindenbaum_equiv L p p.
Proof.
  intros AtomType L Hclass p.
  unfold lindenbaum_equiv.
  apply logic_iff_intro; [exact Hclass | |];
    now apply logic_identity.
Qed.

(** Source [ProvablyEquivalent.symm]. *)
Lemma lindenbaum_equiv_sym :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q,
    lindenbaum_equiv L p q -> lindenbaum_equiv L q p.
Proof.
  intros AtomType L Hclass p q Hpq.
  unfold lindenbaum_equiv in *.
  now apply (logic_iff_sym Hclass).
Qed.

(** Source [ProvablyEquivalent.trans]. *)
Lemma lindenbaum_equiv_trans :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p q r,
    lindenbaum_equiv L p q ->
    lindenbaum_equiv L q r ->
    lindenbaum_equiv L p r.
Proof.
  intros AtomType L Hclass p q r Hpq Hqr.
  unfold lindenbaum_equiv in *.
  eapply logic_iff_trans; eauto.
Qed.

Local Ltac solve_lindenbaum_classical Hclass :=
  apply (logic_classical_tautology Hclass);
  intro rho; unfold Iff, And, Or, Neg, Top; simpl; tauto.

Lemma lindenbaum_imp_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (Imp p q) (Imp p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

Lemma lindenbaum_and_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (And p q) (And p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

Lemma lindenbaum_or_respects_equiv :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p p' q q',
    lindenbaum_equiv L p p' ->
    lindenbaum_equiv L q q' ->
    lindenbaum_equiv L (Or p q) (Or p' q').
Proof.
  intros AtomType L Hclass p p' q q' Hpp Hqq.
  unfold lindenbaum_equiv in *.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  solve_lindenbaum_classical Hclass.
Qed.

(** * The Boolean algebra *)

(** This is specifically Foundation's classical [BooleanAlgebra] instance.
    The repository's [boolean_algebra] record subsumes the order and operation
    laws used by that instance.  Foundation's weaker generalized-Heyting and
    intuitionistic boundaries remain outside this classical API: modal
    conjunction and disjunction in [formula] are themselves classically
    encoded. *)
Definition lindenbaum_boolean_algebra
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) :
    boolean_algebra (formula AtomType).
Proof.
  refine
    {| ba_equiv := lindenbaum_equiv L;
       ba_le := lindenbaum_le L;
       ba_top := Top;
       ba_bottom := Bottom;
       ba_meet := And;
       ba_join := Or;
       ba_compl := Neg;
       ba_imp := Imp |}.
  - split.
    + intro p.
      exact (@lindenbaum_equiv_refl AtomType L Hclass p).
    + intros p q Hpq.
      exact (@lindenbaum_equiv_sym AtomType L Hclass p q Hpq).
    + intros p q r Hpq Hqr.
      exact (@lindenbaum_equiv_trans AtomType L Hclass p q r Hpq Hqr).
  - split.
    + intro p. unfold lindenbaum_le. now apply logic_identity.
    + intros p q r Hpq Hqr. unfold lindenbaum_le in *.
      eapply logic_imp_trans; eauto.
  - intros p q Hpq Hqp. unfold lindenbaum_equiv, lindenbaum_le in *.
    now apply (logic_iff_intro Hclass).
  - intros p p' Hpp q q' Hqq; split; intro Hpq;
      unfold lindenbaum_equiv, lindenbaum_le in *.
    + eapply logic_imp_trans; [exact Hclass | |].
      * exact (@logic_iff_elim_right AtomType L Hclass p p' Hpp).
      * eapply logic_imp_trans; [exact Hclass | exact Hpq |].
        exact (@logic_iff_elim_left AtomType L Hclass q q' Hqq).
    + eapply logic_imp_trans; [exact Hclass | |].
      * exact (@logic_iff_elim_left AtomType L Hclass p p' Hpp).
      * eapply logic_imp_trans; [exact Hclass | exact Hpq |].
        exact (@logic_iff_elim_right AtomType L Hclass q q' Hqq).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_and_respects_equiv Hclass).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_or_respects_equiv Hclass).
  - intros p q Hpq. unfold lindenbaum_equiv in *.
    now apply (logic_neg_iff Hclass).
  - intros p p' Hpp q q' Hqq.
    now apply (lindenbaum_imp_respects_equiv Hclass).
  - intro p. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q r Hpq Hpr. unfold lindenbaum_le in *.
    now apply (logic_imp_and_intro Hclass).
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_lindenbaum_classical Hclass.
  - intros p q r Hpr Hqr. unfold lindenbaum_le in *.
    eapply (logic_modus_ponens Hclass); [|exact Hqr].
    eapply (logic_modus_ponens Hclass); [|exact Hpr].
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q r. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q Hpq. unfold lindenbaum_le in *.
    now apply (logic_contraposition Hclass).
  - unfold lindenbaum_equiv. solve_lindenbaum_classical Hclass.
  - unfold lindenbaum_equiv. solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intro p. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros p q. unfold lindenbaum_equiv.
    solve_lindenbaum_classical Hclass.
  - intros x p q; split; intro H; unfold lindenbaum_le in *.
    + now apply (logic_curry Hclass).
    + eapply (logic_modus_ponens Hclass); [|exact H].
      solve_lindenbaum_classical Hclass.
Defined.

(** * Readback and beta laws *)

(** Setoid counterpart of source [of_eq_of]. *)
Lemma lindenbaum_equiv_readback :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_equiv (lindenbaum_boolean_algebra Hclass) p q <->
    L (Iff p q).
Proof. reflexivity. Qed.

(** Source [le_def]. *)
Lemma lindenbaum_order_readback :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_le (lindenbaum_boolean_algebra Hclass) p q <->
    L (Imp p q).
Proof. reflexivity. Qed.

(** Source [top_def]. *)
Lemma lindenbaum_top_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    ba_top (lindenbaum_boolean_algebra Hclass) = Top.
Proof. reflexivity. Qed.

(** Source [bot_def]. *)
Lemma lindenbaum_bottom_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    ba_bottom (lindenbaum_boolean_algebra Hclass) = Bottom.
Proof. reflexivity. Qed.

(** Source [inf_def]. *)
Lemma lindenbaum_meet_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_meet (lindenbaum_boolean_algebra Hclass) p q = And p q.
Proof. reflexivity. Qed.

(** Source [sup_def]. *)
Lemma lindenbaum_join_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_join (lindenbaum_boolean_algebra Hclass) p q = Or p q.
Proof. reflexivity. Qed.

(** Source [himp_def]. *)
Lemma lindenbaum_imp_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p q,
    ba_imp (lindenbaum_boolean_algebra Hclass) p q = Imp p q.
Proof. reflexivity. Qed.

(** Source [compl_def]. *)
Lemma lindenbaum_compl_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p,
    ba_compl (lindenbaum_boolean_algebra Hclass) p = Neg p.
Proof. reflexivity. Qed.

(** * Provability, consistency, and nontriviality *)

(** Source [provable_iff_provablyEquivalent_verum] and
    [provable_iff_eq_top], combined for the setoid presentation. *)
Lemma lindenbaum_provable_iff_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L) p,
    L p <->
    ba_equiv (lindenbaum_boolean_algebra Hclass) p
      (ba_top (lindenbaum_boolean_algebra Hclass)).
Proof.
  intros AtomType L Hclass p.
  change (L p <-> L (Iff p Top)).
  split.
  - now apply logic_iff_top_left_from.
  - intro Hiff.
    eapply (logic_modus_ponens Hclass).
    + exact (@logic_iff_elim_right AtomType L Hclass p Top Hiff).
    + now apply logic_mem_top.
Qed.

Definition lindenbaum_trivial
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) : Prop :=
  forall p : formula AtomType,
    ba_equiv (lindenbaum_boolean_algebra Hclass) p
      (ba_top (lindenbaum_boolean_algebra Hclass)).

Definition lindenbaum_nontrivial
    (AtomType : Type) (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) : Prop :=
  exists p q : formula AtomType,
    ~ ba_equiv (lindenbaum_boolean_algebra Hclass) p q.

(** Source [inconsistent_iff_trivial]. *)
Lemma lindenbaum_inconsistent_iff_trivial :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_inconsistent L <->
    lindenbaum_trivial Hclass.
Proof.
  intros AtomType L Hclass; split.
  - intros Hinconsistent p.
    apply (proj1 (lindenbaum_provable_iff_top Hclass p)).
    exact (Hinconsistent p).
  - intros Htrivial p.
    apply (proj2 (lindenbaum_provable_iff_top Hclass p)).
    exact (Htrivial p).
Qed.

(** Source [consistent_iff_nontrivial]. *)
Lemma lindenbaum_consistent_iff_nontrivial :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_consistent L <->
    lindenbaum_nontrivial Hclass.
Proof.
  intros AtomType L Hclass; split.
  - intro Hconsistent.
    destruct (logic_exists_unprovable Hconsistent) as [p Hp].
    exists p, Top. intro Hequiv.
    apply Hp.
    apply (proj2 (lindenbaum_provable_iff_top Hclass p)).
    exact Hequiv.
  - intros [p [q Hneq]] Hinconsistent.
    apply Hneq. exact (Hinconsistent (Iff p q)).
Qed.

(** Source [nontrivial_of_consistent]. *)
Lemma lindenbaum_nontrivial_of_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType)
         (Hclass : classical_logic L),
    logic_consistent L -> lindenbaum_nontrivial Hclass.
Proof.
  intros AtomType L Hclass Hconsistent.
  now apply (proj1 (lindenbaum_consistent_iff_nontrivial Hclass)).
Qed.
