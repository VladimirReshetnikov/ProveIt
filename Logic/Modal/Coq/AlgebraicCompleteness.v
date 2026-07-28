(**
  The syntactic Lindenbaum model and algebraic completeness.

  This file independently ports the thirteen remaining active declarations
  at lines 19--60 and 151--189 of the pinned Foundation module
  [Modal/Algebra/Basic.lean].  Coq's carrier is the formula type itself and
  provable biconditional is its setoid equality.  Thus no quotient type or
  choice of representatives is needed; this is extensionally the same
  Lindenbaum algebra used by Foundation.

  Foundation states declarations 1--5 over an abstract connective carrier.
  This repository's modal layer has the concrete syntax [formula AtomType],
  so their generic counterpart quantifies over every atom type and every
  entailment predicate [L] equipped with [k_entailment].  The setoid
  presentation also removes the source's implementation-only [DecidableEq]
  requirement.

  The Boolean laws are discharged through the raw calculus's classical
  propositional completeness.  That completeness is obtained by the same
  finite-skeleton/box-erasure argument already used for [HilbertWithRE],
  adapted here to [normal_hilbert_proves].  Modal K supplies congruence of
  box and preservation of conjunction.  The resulting model proves the
  generic algebraic completeness theorem directly, including the
  inconsistent-system branch.
*)

From Stdlib Require Import
  Logic.ClassicalDescription Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax HilbertK LogicInfrastructure EntailmentExtensions
  HilbertAxiom HilbertNormal HilbertNormalAxiomAdapters
  HilbertWithREClassicalCompleteness CanonicalK ModalAlgebra
  AlgebraicSemantics HilbertNormalBaseSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Classical propositional completeness of the raw normal basis *)

Local Definition normal_hilbert_empty_axioms {AtomType : Type}
    : raw_modal_axiom AtomType :=
  fun _ => False.

Local Fixpoint normal_hilbert_erase_boxes {AtomType : Type}
    (p : formula AtomType) : formula AtomType :=
  match p with
  | Atom a => Atom a
  | Bottom => Bottom
  | Imp q r => Imp (normal_hilbert_erase_boxes q)
                   (normal_hilbert_erase_boxes r)
  | Box _ => Top
  end.

Local Lemma normal_hilbert_empty_identity :
  forall (AtomType : Type) (p : formula AtomType),
    normal_hilbert_proves (@normal_hilbert_empty_axioms AtomType)
      (Imp p p).
Proof. intros; apply normal_hilbert_identity. Qed.

Local Lemma normal_hilbert_empty_top :
  forall AtomType : Type,
    normal_hilbert_proves (@normal_hilbert_empty_axioms AtomType) Top.
Proof. intro AtomType; exact (normal_hilbert_empty_identity Bottom). Qed.

Local Lemma K_proves_erase_boxes_normal_hilbert :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves p ->
    normal_hilbert_proves (@normal_hilbert_empty_axioms AtomType)
      (normal_hilbert_erase_boxes p).
Proof.
  intros AtomType p Hp; induction Hp; simpl.
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - exact (NH_imply_K Top Top).
  - exact (NH_mp IHHp1 IHHp2).
  - apply normal_hilbert_empty_top.
Qed.

Local Lemma normal_hilbert_empty_substitute_between :
  forall (A B : Type) (sigma : A -> formula B) p,
    normal_hilbert_proves (@normal_hilbert_empty_axioms A) p ->
    normal_hilbert_proves (@normal_hilbert_empty_axioms B)
      (substitute sigma p).
Proof.
  intros A B sigma p Hp; induction Hp; simpl.
  - contradiction.
  - exact (NH_mp IHHp1 IHHp2).
  - exact (NH_nec IHHp).
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
Qed.

Local Lemma normal_hilbert_erase_skeleton :
  forall (AtomType : Type) (support : list (formula AtomType)) p,
    normal_hilbert_erase_boxes
      (with_re_propositional_skeleton support p) =
    with_re_propositional_skeleton support p.
Proof.
  intros AtomType support p; induction p; simpl; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Local Theorem normal_hilbert_empty_classical_complete :
  forall (AtomType : Type) p,
    classical_tautology p ->
    normal_hilbert_proves (@normal_hilbert_empty_axioms AtomType) p.
Proof.
  intros AtomType p Htaut.
  set (support := with_re_propositional_support p).
  set (skeleton := with_re_propositional_skeleton support p).
  assert (Hskeleton_taut : classical_tautology skeleton).
  { subst skeleton. now apply with_re_skeleton_tautology. }
  assert (Hskeleton_K : K_proves skeleton).
  { apply K_complete, classical_tautology_valid. exact Hskeleton_taut. }
  pose proof
    (K_proves_erase_boxes_normal_hilbert Hskeleton_K) as Hnormal.
  assert (Herase : normal_hilbert_erase_boxes skeleton = skeleton).
  { subst skeleton. apply normal_hilbert_erase_skeleton. }
  rewrite Herase in Hnormal.
  pose proof
    (normal_hilbert_empty_substitute_between
      (with_re_support_decode support) Hnormal) as Hdecoded.
  subst skeleton support.
  now rewrite with_re_decode_own_skeleton in Hdecoded.
Qed.

Local Corollary normal_hilbert_classical_complete :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    classical_tautology p -> normal_hilbert_proves Ax p.
Proof.
  intros AtomType Ax p Htaut.
  eapply
    (@normal_hilbert_weaker_of_subset_axioms AtomType
      (@normal_hilbert_empty_axioms AtomType) Ax).
  - intros q Hempty. contradiction.
  - now apply normal_hilbert_empty_classical_complete.
Qed.

Local Definition normal_hilbert_classical_logic
    (AtomType : Type) (Ax : raw_modal_axiom AtomType) :
    classical_logic (@normal_hilbert_proves AtomType Ax).
Proof.
  constructor.
  - intros p Hp. now apply normal_hilbert_classical_complete.
  - intros p q Hpq Hp. exact (NH_mp Hpq Hp).
Defined.

(** * The formula presentation of the Lindenbaum modal algebra *)

Local Definition lindenbaum_equiv {AtomType}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Iff p q).

Local Definition lindenbaum_le {AtomType}
    (L : modal_logic_set AtomType)
    (p q : formula AtomType) : Prop :=
  L (Imp p q).

Local Ltac solve_classical Hclass :=
  apply (logic_classical_tautology Hclass);
  intro rho; unfold Iff, And, Or, Neg, Top; simpl; tauto.

Local Lemma lindenbaum_imp_respects_equiv :
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
  solve_classical Hclass.
Qed.

Local Lemma lindenbaum_and_respects_equiv :
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
  solve_classical Hclass.
Qed.

Local Lemma lindenbaum_or_respects_equiv :
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
  solve_classical Hclass.
Qed.

Local Definition lindenbaum_boolean_algebra
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
    + intro p. unfold lindenbaum_equiv.
      apply logic_iff_intro; [exact Hclass | |]; apply logic_identity;
        exact Hclass.
    + intros p q Hpq. unfold lindenbaum_equiv in *.
      now apply (logic_iff_sym Hclass).
    + intros p q r Hpq Hqr. unfold lindenbaum_equiv in *.
      eapply logic_iff_trans; eauto.
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
  - intro p. unfold lindenbaum_le. solve_classical Hclass.
  - intro p. unfold lindenbaum_le. solve_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_classical Hclass.
  - intros p q r Hpq Hpr. unfold lindenbaum_le in *.
    now apply (logic_imp_and_intro Hclass).
  - intros p q. unfold lindenbaum_le. solve_classical Hclass.
  - intros p q. unfold lindenbaum_le. solve_classical Hclass.
  - intros p q r Hpr Hqr. unfold lindenbaum_le in *.
    eapply (logic_modus_ponens Hclass); [|exact Hqr].
    eapply (logic_modus_ponens Hclass); [|exact Hpr].
    solve_classical Hclass.
  - intros p q. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q r. unfold lindenbaum_equiv. solve_classical Hclass.
  - intro p. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q Hpq. unfold lindenbaum_le in *.
    now apply (logic_contraposition Hclass).
  - unfold lindenbaum_equiv. solve_classical Hclass.
  - unfold lindenbaum_equiv. solve_classical Hclass.
  - intro p. unfold lindenbaum_equiv. solve_classical Hclass.
  - intro p. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros p q. unfold lindenbaum_equiv. solve_classical Hclass.
  - intros x p q; split; intro H; unfold lindenbaum_le in *.
    + now apply (logic_curry Hclass).
    + eapply (logic_modus_ponens Hclass); [|exact H].
      solve_classical Hclass.
Defined.

(** * The five source declarations that equip the Lindenbaum algebra *)

(** Source declaration 1/13: the [Box (LindenbaumAlgebra S)] instance.
    On representatives the operation is syntactic box. *)
Definition lindenbaum_box {AtomType : Type}
    (L : modal_logic_set AtomType) (p : formula AtomType) :
    formula AtomType :=
  Box p.

(** Source declaration 2/13: the [Dia (LindenbaumAlgebra S)] instance.
    On representatives the operation is syntactic diamond. *)
Definition lindenbaum_dia {AtomType : Type}
    (L : modal_logic_set AtomType) (p : formula AtomType) :
    formula AtomType :=
  Dia p.

(** Source declaration 3/13: [LindenbaumAlgebra.box_def].  Retaining
    representatives strengthens quotient equality to Coq equality. *)
Lemma lindenbaum_box_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType) p,
    lindenbaum_box L p = Box p.
Proof. reflexivity. Qed.

(** Source declaration 4/13: [LindenbaumAlgebra.dia_def].  Retaining
    representatives strengthens quotient equality to Coq equality. *)
Lemma lindenbaum_dia_beta :
  forall (AtomType : Type) (L : modal_logic_set AtomType) p,
    lindenbaum_dia L p = Dia p.
Proof. reflexivity. Qed.

(** Source declaration 5/13: [LindenbaumAlgebra.instModalAlgebra]. *)
Definition lindenbaum_modal_algebra
    (AtomType : Type) (L : modal_logic_set AtomType)
    (HK : k_entailment L) :
    modal_algebra (formula AtomType).
Proof.
  pose proof (k_classical HK) as Hclass.
  refine
    {| modal_boolean := @lindenbaum_boolean_algebra AtomType L Hclass;
       modal_box := lindenbaum_box L;
       modal_dia := lindenbaum_dia L |}.
  - intros p q Hpq.
    change (L (Iff p q)) in Hpq.
    change (L (Iff (Box p) (Box q))).
    apply logic_iff_intro; [exact Hclass | |].
    + apply (box_regularity_of_k HK).
      now apply (logic_iff_elim_left Hclass).
    + apply (box_regularity_of_k HK).
      now apply (logic_iff_elim_right Hclass).
  - intros p q Hpq.
    change (L (Iff p q)) in Hpq.
    change (L (Iff (Dia p) (Dia q))).
    unfold Dia.
    apply logic_neg_iff; [exact Hclass |].
    apply logic_iff_intro; [exact Hclass | |].
    + apply (box_regularity_of_k HK).
      apply (logic_iff_elim_left Hclass).
      now apply (logic_neg_iff Hclass).
    + apply (box_regularity_of_k HK).
      apply (logic_iff_elim_right Hclass).
      now apply (logic_neg_iff Hclass).
  - change (L (Iff (Box Top) Top)).
    apply logic_iff_top_left_from; [exact Hclass |].
    apply (k_necessitation HK).
    now apply logic_mem_top.
  - intros p q.
    change (L (Iff (Box (And p q)) (And (Box p) (Box q)))).
    apply logic_iff_intro; [exact Hclass | |].
    + apply logic_imp_and_intro; [exact Hclass | |].
      * apply (box_regularity_of_k HK).
        now apply logic_and_elim_left_imp.
      * apply (box_regularity_of_k HK).
        now apply logic_and_elim_right_imp.
    + exact (has_C_axiom (has_C_of_k HK) p q).
  - intro p.
    change (L (Iff (Dia p) (Neg (Box (Neg p))))).
    exact (k_dia_duality HK p).
Defined.

(** * The late eight algebraic-semantics declarations *)

Local Definition normal_hilbert_k_entailment
    (AtomType : Type) (Ax : raw_modal_axiom AtomType)
    (HK : has_K (@normal_hilbert_proves AtomType Ax)) :
    k_entailment (@normal_hilbert_proves AtomType Ax).
Proof.
  constructor.
  - exact (@normal_hilbert_classical_logic AtomType Ax).
  - exact (@normal_hilbert_necessitation AtomType Ax).
  - exact HK.
  - intro p.
    exact (has_DiaDuality_axiom
      (@normal_hilbert_has_DiaDuality AtomType Ax) p).
Defined.

(** Source declaration 6/13: [AlgebraicSemantics.lindenbaum].  The carrier
    retains formula representatives and uses provable biconditional as its
    setoid equality. *)
Definition algebraic_lindenbaum
    (AtomType : Type) (Ax : raw_modal_axiom AtomType)
    (HK : has_K (@normal_hilbert_proves AtomType Ax))
    (Hconsistent : ~ normal_hilbert_proves Ax Bottom) :
    algebraic_semantics AtomType.
Proof.
  pose proof (@normal_hilbert_classical_logic AtomType Ax) as Hclass.
  pose proof (@normal_hilbert_k_entailment AtomType Ax HK) as HKent.
  refine
    {| algebraic_carrier := formula AtomType;
       algebraic_valuation := @Atom AtomType;
       algebraic_modal := @lindenbaum_modal_algebra AtomType
         (@normal_hilbert_proves AtomType Ax) HKent |}.
  exists Bottom, Top.
  change (~ normal_hilbert_proves Ax (Iff Bottom Top)).
  intro Hiff. apply Hconsistent.
  eapply (logic_modus_ponens Hclass).
  - exact (@logic_iff_elim_right AtomType
      (@normal_hilbert_proves AtomType Ax) Hclass Bottom Top Hiff).
  - exact (@logic_mem_top AtomType
      (@normal_hilbert_proves AtomType Ax) Hclass).
Defined.

(** Source declaration 7/13: [AlgebraicSemantics.lindenbaum_val_eq].
    Retaining representatives strengthens quotient equality to literal
    equality. *)
Lemma algebraic_lindenbaum_value :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (HK : has_K (@normal_hilbert_proves AtomType Ax))
         (Hconsistent : ~ normal_hilbert_proves Ax Bottom)
         (p : formula AtomType),
    algebraic_formula_value
      (ba_bottom
        (modal_boolean (algebraic_modal
          (algebraic_lindenbaum HK Hconsistent))))
      (ba_imp
        (modal_boolean (algebraic_modal
          (algebraic_lindenbaum HK Hconsistent))))
      (modal_box (algebraic_modal
        (algebraic_lindenbaum HK Hconsistent)))
      (algebraic_valuation (algebraic_lindenbaum HK Hconsistent)) p = p.
Proof.
  intros AtomType Ax HK Hconsistent p.
  change (algebraic_formula_value Bottom Imp Box (@Atom AtomType) p = p).
  induction p; simpl; now f_equal.
Qed.

(** Source declaration 8/13: [AlgebraicSemantics.lindenbaum_complete_iff]. *)
Lemma algebraic_lindenbaum_complete_iff :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (HK : has_K (@normal_hilbert_proves AtomType Ax))
         (Hconsistent : ~ normal_hilbert_proves Ax Bottom)
         (p : formula AtomType),
    algebraic_semantics_satisfies
      (algebraic_lindenbaum HK Hconsistent) p <->
    normal_hilbert_proves Ax p.
Proof.
  intros AtomType Ax HK Hconsistent p.
  pose proof (@normal_hilbert_classical_logic AtomType Ax) as Hclass.
  unfold algebraic_semantics_satisfies.
  rewrite (algebraic_lindenbaum_value HK Hconsistent p).
  change (normal_hilbert_proves Ax (Iff p Top) <->
    normal_hilbert_proves Ax p).
  split.
  - intro Hiff.
    eapply (logic_modus_ponens Hclass).
    + exact (@logic_iff_elim_right AtomType
        (@normal_hilbert_proves AtomType Ax) Hclass p Top Hiff).
    + exact (@logic_mem_top AtomType
        (@normal_hilbert_proves AtomType Ax) Hclass).
  - intro Hp.
    exact (@logic_iff_top_left_from AtomType
      (@normal_hilbert_proves AtomType Ax) Hclass p Hp).
Qed.

(** Source declaration 9/13: the fixed-Lindenbaum [Sound] instance. *)
Definition algebraic_lindenbaum_sound_instance :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (HK : has_K (@normal_hilbert_proves AtomType Ax))
         (Hconsistent : ~ normal_hilbert_proves Ax Bottom)
         (p : formula AtomType),
    normal_hilbert_proves Ax p ->
    algebraic_semantics_satisfies
      (algebraic_lindenbaum HK Hconsistent) p :=
  fun AtomType Ax HK Hconsistent p =>
    proj2 (algebraic_lindenbaum_complete_iff HK Hconsistent p).

(** Source declaration 10/13: the fixed-Lindenbaum [Complete] instance. *)
Definition algebraic_lindenbaum_complete_instance :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (HK : has_K (@normal_hilbert_proves AtomType Ax))
         (Hconsistent : ~ normal_hilbert_proves Ax Bottom)
         (p : formula AtomType),
    algebraic_semantics_satisfies
      (algebraic_lindenbaum HK Hconsistent) p ->
    normal_hilbert_proves Ax p :=
  fun AtomType Ax HK Hconsistent p =>
    proj1 (algebraic_lindenbaum_complete_iff HK Hconsistent p).

(** Source declaration 11/13: [AlgebraicSemantics.complete]. *)
Lemma normal_hilbert_algebraic_complete :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    has_K (@normal_hilbert_proves AtomType Ax) ->
    forall p : formula AtomType,
      (forall S : algebraic_semantics AtomType,
        algebraic_mod Ax S ->
        algebraic_semantics_satisfies S p) ->
      normal_hilbert_proves Ax p.
Proof.
  intros AtomType Ax HK p Hvalid.
  pose proof (@normal_hilbert_classical_logic AtomType Ax) as Hclass.
  destruct (classic (normal_hilbert_proves Ax Bottom))
    as [Hinconsistent | Hconsistent].
  - eapply (logic_modus_ponens Hclass); [|exact Hinconsistent].
    solve_classical Hclass.
  - apply (proj1 (algebraic_lindenbaum_complete_iff
      HK Hconsistent p)).
    apply Hvalid.
    intros q Hinstance.
    apply (proj2 (algebraic_lindenbaum_complete_iff
      HK Hconsistent q)).
    destruct Hinstance as [template [Htemplate [sigma ->]]].
    exact (@NH_axm AtomType Ax template sigma Htemplate).
Qed.

(** Source declaration 12/13: [AlgebraicSemantics.instCompleteMod]. *)
Definition normal_hilbert_algebraic_complete_instance :=
  @normal_hilbert_algebraic_complete.

(** Source declaration 13/13: algebraic completeness of the named raw K
    system. *)
Definition normal_K_algebraic_complete_instance :
  forall p : formula nat,
    (forall S : algebraic_semantics nat,
      algebraic_mod normal_K_axioms S ->
      algebraic_semantics_satisfies S p) ->
    normal_K p :=
  @normal_hilbert_algebraic_complete nat normal_K_axioms
    (structural_k_K normal_K_entailment).
