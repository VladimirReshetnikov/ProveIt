(**
  Generic algebraic semantics and soundness for raw normal Hilbert systems.

  This file independently ports the exact twenty-six active declarations at
  lines 64--146 of the pinned Foundation module
  [Modal/Algebra/Basic.lean].  The quotient/Lindenbaum construction before
  and after that bounded tranche is deliberately excluded.

  Foundation uses ordinary equality on Boolean algebras.  [ModalAlgebra]
  instead presents equality as the setoid relation [ba_equiv], so every
  source equality is translated to that relation.  This is the compatible
  formulation for the existing powerset algebra, and keeps the complete
  development constructive.  A source [Nontrivial] carrier is correspondingly
  represented by two elements that are not setoid-equivalent.
*)

From FoundationModal Require Import
  Syntax HilbertK HilbertAxiom HilbertNormal ModalAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Formula evaluation *)

(** Source declaration 1/26: [Modal.Formula.value].  As in the source, the
    evaluator requires only interpretations of primitive falsity,
    implication, and box; it is not tied to a modal algebra. *)
Fixpoint algebraic_formula_value {AtomType H : Type}
    (bottom : H) (himp : H -> H -> H) (box : H -> H)
    (V : AtomType -> H) (p : formula AtomType) : H :=
  match p with
  | Atom a => V a
  | Bottom => bottom
  | Imp q r =>
      himp
        (algebraic_formula_value bottom himp box V q)
        (algebraic_formula_value bottom himp box V r)
  | Box q => box (algebraic_formula_value bottom himp box V q)
  end.

(** The modal-algebra specialization is private notation for declarations
    2--26, whose source context supplies a [ModalAlgebra].  It expands in
    public types, leaving no additional helper in the exported surface. *)
Local Notation "'modal_formula_value' M V p" :=
  (algebraic_formula_value
    (ba_bottom (modal_boolean M))
    (ba_imp (modal_boolean M))
    (modal_box M) V p)
  (at level 10, M at next level, V at next level, p at next level).

Local Lemma algebraic_formula_value_neg_private :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Neg p))
      (ba_compl (modal_boolean M) (modal_formula_value M V p)).
Proof.
  intros AtomType A M V p.
  unfold Neg; simpl.
  eapply ba_equiv_trans.
  - apply ba_imp_definition.
  - apply ba_join_bottom.
Qed.

(** Source declaration 2/26: [Modal.Formula.eq_value_verum]. *)
Lemma algebraic_formula_value_top :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A),
    ba_equiv (modal_boolean M)
      (modal_formula_value M V Top)
      (ba_top (modal_boolean M)).
Proof.
  intros AtomType A M V.
  unfold Top, Neg; simpl.
  eapply ba_equiv_trans.
  - apply ba_imp_definition.
  - eapply ba_equiv_trans.
    + apply ba_join_respects_equiv.
      * apply ba_compl_bottom.
      * apply ba_equiv_refl.
    + apply ba_join_bottom.
Qed.

(** Source declaration 3/26: [Modal.Formula.eq_value_falsum]. *)
Lemma algebraic_formula_value_bottom :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A),
    ba_equiv (modal_boolean M)
      (modal_formula_value M V Bottom)
      (ba_bottom (modal_boolean M)).
Proof. intros; simpl; apply ba_equiv_refl. Qed.

(** Source declaration 4/26: [Modal.Formula.eq_value_imp]. *)
Lemma algebraic_formula_value_imp :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p q,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Imp p q))
      (ba_imp (modal_boolean M)
        (modal_formula_value M V p)
        (modal_formula_value M V q)).
Proof. intros; simpl; apply ba_equiv_refl. Qed.

(** Source declaration 5/26: [Modal.Formula.eq_value_and]. *)
Lemma algebraic_formula_value_and :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p q,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (And p q))
      (ba_meet (modal_boolean M)
        (modal_formula_value M V p)
        (modal_formula_value M V q)).
Proof.
  intros AtomType A M V p q.
  unfold And.
  eapply ba_equiv_trans.
  - apply algebraic_formula_value_neg_private.
  - eapply ba_equiv_trans.
    + apply ba_compl_respects_equiv.
      simpl.
      apply ba_imp_respects_equiv.
      * apply ba_equiv_refl.
      * apply algebraic_formula_value_neg_private.
    + eapply ba_equiv_trans.
      * apply ba_compl_respects_equiv.
        apply ba_imp_definition.
      * eapply ba_equiv_trans.
        -- apply ba_de_morgan_join.
        -- apply ba_meet_respects_equiv;
             apply ba_compl_involutive.
Qed.

(** Source declaration 6/26: [Modal.Formula.eq_value_or]. *)
Lemma algebraic_formula_value_or :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p q,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Or p q))
      (ba_join (modal_boolean M)
        (modal_formula_value M V p)
        (modal_formula_value M V q)).
Proof.
  intros AtomType A M V p q.
  unfold Or; simpl.
  eapply ba_equiv_trans.
  - apply ba_imp_respects_equiv.
    + apply algebraic_formula_value_neg_private.
    + apply ba_equiv_refl.
  - eapply ba_equiv_trans.
    + apply ba_imp_definition.
    + apply ba_join_respects_equiv.
      * apply ba_compl_involutive.
      * apply ba_equiv_refl.
Qed.

(** Source declaration 7/26: [Modal.Formula.eq_value_neg]. *)
Lemma algebraic_formula_value_neg :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Neg p))
      (ba_compl (modal_boolean M) (modal_formula_value M V p)).
Proof. exact algebraic_formula_value_neg_private. Qed.

(** Source declaration 8/26: [Modal.Formula.eq_value_box]. *)
Lemma algebraic_formula_value_box :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Box p))
      (modal_box M (modal_formula_value M V p)).
Proof. intros; simpl; apply ba_equiv_refl. Qed.

(** Source declaration 9/26: [Modal.Formula.eq_value_dia]. *)
Lemma algebraic_formula_value_dia :
  forall (AtomType A : Type) (M : modal_algebra A)
         (V : AtomType -> A) p,
    ba_equiv (modal_boolean M)
      (modal_formula_value M V (Dia p))
      (modal_dia M (modal_formula_value M V p)).
Proof.
  intros AtomType A M V p.
  unfold Dia.
  eapply ba_equiv_trans.
  - apply algebraic_formula_value_neg_private.
  - eapply ba_equiv_trans.
    + apply ba_compl_respects_equiv.
      simpl.
      apply modal_box_respects_equiv.
      apply algebraic_formula_value_neg_private.
    + apply ba_equiv_sym.
      apply modal_dia_dual.
Qed.

(** * Algebraic models and their basic semantic laws *)

(** Source declaration 10/26: [Modal.AlgebraicSemantics].  The source field
    order is retained. *)
Record algebraic_semantics (AtomType : Type) : Type := {
  algebraic_carrier : Type;
  algebraic_valuation : AtomType -> algebraic_carrier;
  algebraic_modal : modal_algebra algebraic_carrier;
  algebraic_nontrivial :
    exists x y : algebraic_carrier,
      ~ ba_equiv (modal_boolean algebraic_modal) x y
}.

Arguments algebraic_carrier {AtomType} _.
Arguments algebraic_valuation {AtomType} _ _.
Arguments algebraic_modal {AtomType} _.
Arguments algebraic_nontrivial {AtomType} _.

(** Source declaration 11/26: the [CoeSort] instance. *)
Definition algebraic_semantics_sort {AtomType}
    (S : algebraic_semantics AtomType) : Type :=
  algebraic_carrier S.

(** Source declaration 12/26: the [CoeFun] valuation instance. *)
Definition algebraic_semantics_valuation {AtomType}
    (S : algebraic_semantics AtomType) :
    AtomType -> algebraic_semantics_sort S :=
  algebraic_valuation S.

(** Source declaration 13/26: the inherited [ModalAlgebra] instance. *)
Definition algebraic_semantics_modal {AtomType}
    (S : algebraic_semantics AtomType) :
    modal_algebra (algebraic_semantics_sort S) :=
  algebraic_modal S.

(** Source declaration 14/26: the inherited [Nontrivial] instance. *)
Definition algebraic_semantics_nontrivial {AtomType}
    (S : algebraic_semantics AtomType) :
    exists x y : algebraic_semantics_sort S,
      ~ ba_equiv (modal_boolean (algebraic_semantics_modal S)) x y :=
  algebraic_nontrivial S.

(** Source declaration 15/26: the formula [Semantics] instance. *)
Definition algebraic_semantics_satisfies {AtomType}
    (S : algebraic_semantics AtomType) (p : formula AtomType) : Prop :=
  ba_equiv (modal_boolean (algebraic_modal S))
    (modal_formula_value (algebraic_modal S)
      (algebraic_valuation S) p)
    (ba_top (modal_boolean (algebraic_modal S))).

(** Source declaration 16/26: [AlgebraicSemantics.def_val]. *)
Lemma algebraic_satisfies_iff :
  forall (AtomType : Type) (S : algebraic_semantics AtomType) p,
    algebraic_semantics_satisfies S p <->
    ba_equiv (modal_boolean (algebraic_modal S))
      (modal_formula_value (algebraic_modal S)
        (algebraic_valuation S) p)
      (ba_top (modal_boolean (algebraic_modal S))).
Proof. reflexivity. Qed.

Local Lemma ba_bottom_not_equiv_top_of_nontrivial :
  forall (A : Type) (B : boolean_algebra A),
    (exists x y, ~ ba_equiv B x y) ->
    ~ ba_equiv B (ba_bottom B) (ba_top B).
Proof.
  intros A B [x [y Hxy]] Hbt.
  apply Hxy.
  eapply ba_equiv_trans with (b := ba_top B).
  - apply ba_le_antisymmetric.
    + apply ba_le_top.
    + apply (@ba_le_respect_left A B
        (ba_bottom B) (ba_top B) x Hbt).
      apply ba_bottom_le.
  - apply ba_equiv_sym.
    apply ba_le_antisymmetric.
    + apply ba_le_top.
    + apply (@ba_le_respect_left A B
        (ba_bottom B) (ba_top B) y Hbt).
      apply ba_bottom_le.
Qed.

Local Lemma ba_meet_equiv_top_iff :
  forall (A : Type) (B : boolean_algebra A) x y,
    ba_equiv B (ba_meet B x y) (ba_top B) <->
    ba_equiv B x (ba_top B) /\ ba_equiv B y (ba_top B).
Proof.
  intros A B x y; split.
  - intro Hmeet; split; apply ba_le_antisymmetric.
    + apply ba_le_top.
    + eapply ba_le_trans.
      * apply ba_equiv_implies_le. apply ba_equiv_sym. exact Hmeet.
      * apply ba_meet_le_left.
    + apply ba_le_top.
    + eapply ba_le_trans.
      * apply ba_equiv_implies_le. apply ba_equiv_sym. exact Hmeet.
      * apply ba_meet_le_right.
  - intros [Hx Hy].
    eapply ba_equiv_trans.
    + exact (@ba_meet_respects_equiv A B
        x (ba_top B) Hx y (ba_top B) Hy).
    + apply ba_top_meet.
Qed.

(** Source declaration 17/26: the [Semantics.Top] instance. *)
Lemma algebraic_satisfies_top :
  forall (AtomType : Type) (S : algebraic_semantics AtomType),
    algebraic_semantics_satisfies S Top.
Proof.
  intros AtomType S.
  unfold algebraic_semantics_satisfies.
  apply algebraic_formula_value_top.
Qed.

(** Source declaration 18/26: the [Semantics.Bot] instance. *)
Lemma algebraic_not_satisfies_bottom :
  forall (AtomType : Type) (S : algebraic_semantics AtomType),
    ~ algebraic_semantics_satisfies S Bottom.
Proof.
  intros AtomType S Hbottom.
  apply (@ba_bottom_not_equiv_top_of_nontrivial
    (algebraic_carrier S) (modal_boolean (algebraic_modal S))).
  - exact (algebraic_nontrivial S).
  - eapply ba_equiv_trans.
    + apply ba_equiv_sym. apply algebraic_formula_value_bottom.
    + exact Hbottom.
Qed.

(** Source declaration 19/26: the [Semantics.And] instance. *)
Lemma algebraic_satisfies_and :
  forall (AtomType : Type) (S : algebraic_semantics AtomType) p q,
    algebraic_semantics_satisfies S (And p q) <->
    algebraic_semantics_satisfies S p /\
      algebraic_semantics_satisfies S q.
Proof.
  intros AtomType S p q.
  unfold algebraic_semantics_satisfies.
  set (M := algebraic_modal S).
  set (V := algebraic_valuation S).
  set (B := modal_boolean M).
  set (x := modal_formula_value M V p).
  set (y := modal_formula_value M V q).
  assert (Hand :
    ba_equiv B (modal_formula_value M V (And p q))
      (ba_meet B x y)).
  { subst B x y V M. apply algebraic_formula_value_and. }
  split.
  - intro H.
    apply (proj1 (ba_meet_equiv_top_iff B x y)).
    eapply ba_equiv_trans.
    + apply ba_equiv_sym. exact Hand.
    + exact H.
  - intro H.
    eapply ba_equiv_trans.
    + exact Hand.
    + apply (proj2 (ba_meet_equiv_top_iff B x y)). exact H.
Qed.

Local Lemma ba_imp_equiv_top_iff :
  forall (A : Type) (B : boolean_algebra A) x y,
    ba_equiv B (ba_imp B x y) (ba_top B) <-> ba_le B x y.
Proof.
  intros A B x y; split.
  - intro Himp.
    eapply (@ba_le_respect_left A B
      (ba_meet B (ba_top B) x) x y).
    + apply ba_top_meet.
    + apply (proj2 (ba_imp_adjoint B (ba_top B) x y)).
      apply ba_equiv_implies_le. apply ba_equiv_sym. exact Himp.
  - apply ba_imp_top_of_le.
Qed.

(** Source declaration 20/26: [AlgebraicSemantics.val_imp]. *)
Lemma algebraic_satisfies_imp :
  forall (AtomType : Type) (S : algebraic_semantics AtomType) p q,
    algebraic_semantics_satisfies S (Imp p q) <->
    ba_le (modal_boolean (algebraic_modal S))
      (modal_formula_value (algebraic_modal S)
        (algebraic_valuation S) p)
      (modal_formula_value (algebraic_modal S)
        (algebraic_valuation S) q).
Proof.
  intros AtomType S p q.
  unfold algebraic_semantics_satisfies; simpl.
  apply ba_imp_equiv_top_iff.
Qed.

(** Source declaration 21/26: [AlgebraicSemantics.nec]. *)
Lemma algebraic_satisfies_nec :
  forall (AtomType : Type) (S : algebraic_semantics AtomType) p,
    algebraic_semantics_satisfies S p ->
    algebraic_semantics_satisfies S (Box p).
Proof.
  intros AtomType S p Hp.
  unfold algebraic_semantics_satisfies in *; simpl.
  eapply ba_equiv_trans.
  - apply modal_box_respects_equiv. exact Hp.
  - apply modal_box_top.
Qed.

(** Source declaration 22/26: [AlgebraicSemantics.mdp]. *)
Lemma algebraic_satisfies_mdp :
  forall (AtomType : Type) (S : algebraic_semantics AtomType) p q,
    algebraic_semantics_satisfies S (Imp p q) ->
    algebraic_semantics_satisfies S p ->
    algebraic_semantics_satisfies S q.
Proof.
  intros AtomType S p q Hpq Hp.
  pose proof (proj1 (algebraic_satisfies_imp S p q) Hpq) as Hle.
  unfold algebraic_semantics_satisfies in *.
  apply ba_le_antisymmetric.
  - apply ba_le_top.
  - eapply ba_le_trans.
    + apply ba_equiv_implies_le. apply ba_equiv_sym. exact Hp.
    + exact Hle.
Qed.

(** * The class of models of raw axioms *)

(** Source declaration 23/26: [AlgebraicSemantics.mod]. *)
Definition algebraic_mod {AtomType : Type}
    (Ax : raw_modal_axiom AtomType)
    (S : algebraic_semantics AtomType) : Prop :=
  forall p, raw_axiom_instances Ax p ->
    algebraic_semantics_satisfies S p.

(** Source declaration 24/26: [AlgebraicSemantics.mod_models_iff].
    Coq spells the source's generic class-validity wrapper explicitly. *)
Lemma algebraic_mod_models_iff :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    (forall S : algebraic_semantics AtomType,
      algebraic_mod Ax S -> algebraic_semantics_satisfies S p) <->
    (forall S : algebraic_semantics AtomType,
      (forall q, raw_axiom_instances Ax q ->
        algebraic_semantics_satisfies S q) ->
      algebraic_semantics_satisfies S p).
Proof. reflexivity. Qed.

Local Lemma ba_mdp_below :
  forall (A : Type) (B : boolean_algebra A) t x y,
    ba_le B t (ba_imp B x y) -> ba_le B t x -> ba_le B t y.
Proof.
  intros A B t x y Himp Hx.
  eapply ba_le_trans.
  - apply ba_le_meet; [apply ba_le_refl | exact Hx].
  - apply (proj2 (ba_imp_adjoint B t x y)). exact Himp.
Qed.

Local Lemma ba_hilbert_K_top :
  forall (A : Type) (B : boolean_algebra A) x y,
    ba_equiv B (ba_imp B x (ba_imp B y x)) (ba_top B).
Proof.
  intros A B x y. apply ba_imp_top_of_le.
  apply (proj1 (ba_imp_adjoint B x y x)).
  apply ba_meet_le_left.
Qed.

Local Lemma ba_hilbert_S_top :
  forall (A : Type) (B : boolean_algebra A) x y z,
    ba_equiv B
      (ba_imp B (ba_imp B x (ba_imp B y z))
        (ba_imp B (ba_imp B x y) (ba_imp B x z)))
      (ba_top B).
Proof.
  intros A B x y z.
  set (a := ba_imp B x (ba_imp B y z)).
  set (b := ba_imp B x y).
  set (t := ba_meet B (ba_meet B a b) x).
  apply ba_imp_top_of_le.
  apply (proj1 (ba_imp_adjoint B a b (ba_imp B x z))).
  apply (proj1 (ba_imp_adjoint B (ba_meet B a b) x z)).
  assert (Ht_a : ba_le B t a).
  { unfold t. eapply ba_le_trans;
      [apply ba_meet_le_left | apply ba_meet_le_left]. }
  assert (Ht_b : ba_le B t b).
  { unfold t. eapply ba_le_trans;
      [apply ba_meet_le_left | apply ba_meet_le_right]. }
  assert (Ht_x : ba_le B t x).
  { unfold t. apply ba_meet_le_right. }
  assert (Ht_yz : ba_le B t (ba_imp B y z)).
  { unfold a in Ht_a.
    exact (@ba_mdp_below A B t x (ba_imp B y z) Ht_a Ht_x). }
  assert (Ht_y : ba_le B t y).
  { unfold b in Ht_b.
    exact (@ba_mdp_below A B t x y Ht_b Ht_x). }
  exact (@ba_mdp_below A B t y z Ht_yz Ht_y).
Qed.

Local Lemma ba_neg_equiv_compl :
  forall (A : Type) (B : boolean_algebra A) x,
    ba_equiv B (ba_imp B x (ba_bottom B)) (ba_compl B x).
Proof.
  intros A B x.
  eapply ba_equiv_trans.
  - apply ba_imp_definition.
  - apply ba_join_bottom.
Qed.

Local Lemma ba_elim_contra_equiv :
  forall (A : Type) (B : boolean_algebra A) x y,
    ba_equiv B
      (ba_imp B
        (ba_imp B y (ba_bottom B))
        (ba_imp B x (ba_bottom B)))
      (ba_imp B x y).
Proof.
  intros A B x y.
  eapply ba_equiv_trans.
  - apply ba_imp_definition.
  - eapply ba_equiv_trans.
    + apply ba_join_respects_equiv.
      * apply ba_compl_respects_equiv. apply ba_neg_equiv_compl.
      * apply ba_neg_equiv_compl.
    + eapply ba_equiv_trans.
      * apply ba_join_respects_equiv.
        -- apply ba_compl_involutive.
        -- apply ba_equiv_refl.
      * eapply ba_equiv_trans.
        -- apply ba_join_commutative.
        -- apply ba_equiv_sym. apply ba_imp_definition.
Qed.

Local Lemma ba_hilbert_elim_contra_top :
  forall (A : Type) (B : boolean_algebra A) x y,
    ba_equiv B
      (ba_imp B
        (ba_imp B
          (ba_imp B y (ba_bottom B))
          (ba_imp B x (ba_bottom B)))
        (ba_imp B x y))
      (ba_top B).
Proof.
  intros A B x y. apply ba_imp_top_of_le.
  apply ba_equiv_implies_le. apply ba_elim_contra_equiv.
Qed.

(** Source declaration 25/26: [AlgebraicSemantics.sound]. *)
Lemma normal_hilbert_algebraic_sound :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    normal_hilbert_proves Ax p ->
    forall S : algebraic_semantics AtomType,
      algebraic_mod Ax S -> algebraic_semantics_satisfies S p.
Proof.
  intros AtomType Ax p Hp; induction Hp; intros S Hmodels.
  - apply Hmodels.
    now apply raw_axiom_instance_of_mem.
  - eapply algebraic_satisfies_mdp; eauto.
  - apply algebraic_satisfies_nec. apply IHHp. exact Hmodels.
  - unfold algebraic_semantics_satisfies, Hilbert_imply_K; simpl.
    apply ba_hilbert_K_top.
  - unfold algebraic_semantics_satisfies, Hilbert_imply_S; simpl.
    apply ba_hilbert_S_top.
  - unfold algebraic_semantics_satisfies, Hilbert_elim_contra, Neg; simpl.
    apply ba_hilbert_elim_contra_top.
Qed.

(** Source declaration 26/26: the [Sound (Hilbert.Normal Ax) (mod Ax)]
    instance.  Since the source-facing Coq layer uses propositions directly
    rather than a generic [Sound] typeclass, the instance is the named alias
    below. *)
Definition normal_hilbert_algebraic_sound_instance :=
  @normal_hilbert_algebraic_sound.
