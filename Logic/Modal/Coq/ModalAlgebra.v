(**
  Boolean modal algebras and Magari algebras.

  Foundation states these results over Lean's bundled Boolean-algebra
  hierarchy.  Here equality is deliberately a setoid relation: this lets the
  powerset algebra of a Kripke frame use pointwise logical equivalence without
  functional or propositional extensionality.

  The Boolean interface exposes the ordinary bounded-lattice, complement,
  De Morgan, distributivity, and Boolean-implication laws.  All modal laws
  below are then derived solely from preservation of top and binary meet and
  from the box/diamond duality equation.  Likewise, a Magari algebra adds only
  its diagonal equation; transitivity is proved, not assumed.
*)

From Stdlib Require Import RelationClasses Morphisms Logic.Classical_Prop.
From FoundationModal Require Import Kripke KripkeAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * A setoid presentation of Boolean algebras *)

Record boolean_algebra (A : Type) := {
  ba_equiv : A -> A -> Prop;
  ba_le : A -> A -> Prop;

  ba_top : A;
  ba_bottom : A;
  ba_meet : A -> A -> A;
  ba_join : A -> A -> A;
  ba_compl : A -> A;
  ba_imp : A -> A -> A;

  ba_equiv_is_equivalence : Equivalence ba_equiv;
  ba_le_is_preorder : PreOrder ba_le;
  ba_le_antisymmetric :
    forall a b, ba_le a b -> ba_le b a -> ba_equiv a b;
  ba_le_respects_equiv :
    Proper (ba_equiv ==> ba_equiv ==> iff) ba_le;

  ba_meet_respects_equiv :
    Proper (ba_equiv ==> ba_equiv ==> ba_equiv) ba_meet;
  ba_join_respects_equiv :
    Proper (ba_equiv ==> ba_equiv ==> ba_equiv) ba_join;
  ba_compl_respects_equiv : Proper (ba_equiv ==> ba_equiv) ba_compl;
  ba_imp_respects_equiv :
    Proper (ba_equiv ==> ba_equiv ==> ba_equiv) ba_imp;

  ba_bottom_le : forall a, ba_le ba_bottom a;
  ba_le_top : forall a, ba_le a ba_top;
  ba_meet_le_left : forall a b, ba_le (ba_meet a b) a;
  ba_meet_le_right : forall a b, ba_le (ba_meet a b) b;
  ba_le_meet : forall a b c, ba_le a b -> ba_le a c ->
    ba_le a (ba_meet b c);
  ba_le_join_left : forall a b, ba_le a (ba_join a b);
  ba_le_join_right : forall a b, ba_le b (ba_join a b);
  ba_join_le : forall a b c, ba_le a c -> ba_le b c ->
    ba_le (ba_join a b) c;

  ba_meet_commutative : forall a b,
    ba_equiv (ba_meet a b) (ba_meet b a);
  ba_join_commutative : forall a b,
    ba_equiv (ba_join a b) (ba_join b a);
  ba_meet_join_distributive : forall a b c,
    ba_equiv (ba_meet a (ba_join b c))
      (ba_join (ba_meet a b) (ba_meet a c));

  ba_compl_involutive : forall a, ba_equiv (ba_compl (ba_compl a)) a;
  ba_compl_antitone : forall a b, ba_le a b ->
    ba_le (ba_compl b) (ba_compl a);
  ba_compl_top : ba_equiv (ba_compl ba_top) ba_bottom;
  ba_compl_bottom : ba_equiv (ba_compl ba_bottom) ba_top;
  ba_meet_compl : forall a,
    ba_equiv (ba_meet a (ba_compl a)) ba_bottom;
  ba_join_compl : forall a,
    ba_equiv (ba_join a (ba_compl a)) ba_top;
  ba_de_morgan_meet : forall a b,
    ba_equiv (ba_compl (ba_meet a b))
      (ba_join (ba_compl a) (ba_compl b));
  ba_de_morgan_join : forall a b,
    ba_equiv (ba_compl (ba_join a b))
      (ba_meet (ba_compl a) (ba_compl b));

  ba_imp_definition : forall a b,
    ba_equiv (ba_imp a b) (ba_join (ba_compl a) b);
  ba_imp_adjoint : forall x a b,
    ba_le (ba_meet x a) b <-> ba_le x (ba_imp a b)
}.

Arguments ba_equiv {A} _ _ _.
Arguments ba_le {A} _ _ _.
Arguments ba_top {A} _.
Arguments ba_bottom {A} _.
Arguments ba_meet {A} _ _ _.
Arguments ba_join {A} _ _ _.
Arguments ba_compl {A} _ _.
Arguments ba_imp {A} _ _ _.

Section BooleanFacts.
  Context {A : Type} (B : boolean_algebra A).

  Lemma ba_equiv_refl : forall a, ba_equiv B a a.
  Proof.
    destruct (ba_equiv_is_equivalence B) as [H _ _]. exact H.
  Qed.

  Lemma ba_equiv_sym : forall a b,
      ba_equiv B a b -> ba_equiv B b a.
  Proof.
    destruct (ba_equiv_is_equivalence B) as [_ H _]. exact H.
  Qed.

  Lemma ba_equiv_trans : forall a b c,
      ba_equiv B a b -> ba_equiv B b c -> ba_equiv B a c.
  Proof.
    destruct (ba_equiv_is_equivalence B) as [_ _ H]. exact H.
  Qed.

  Lemma ba_le_refl : forall a, ba_le B a a.
  Proof.
    destruct (ba_le_is_preorder B) as [H _]. exact H.
  Qed.

  Lemma ba_le_trans : forall a b c,
      ba_le B a b -> ba_le B b c -> ba_le B a c.
  Proof.
    destruct (ba_le_is_preorder B) as [_ H]. exact H.
  Qed.

  Lemma ba_equiv_implies_le : forall a b,
      ba_equiv B a b -> ba_le B a b.
  Proof.
    intros a b Hab.
    pose proof (@ba_le_respects_equiv A B a a (ba_equiv_refl a)
      a b Hab) as Hproper.
    apply (proj1 Hproper). apply ba_le_refl.
  Qed.

  Lemma ba_le_respect_left : forall a a' b,
      ba_equiv B a a' -> ba_le B a b -> ba_le B a' b.
  Proof.
    intros a a' b Haa' Hab.
    pose proof (@ba_le_respects_equiv A B a a' Haa'
      b b (ba_equiv_refl b)) as Hproper.
    now apply (proj1 Hproper).
  Qed.

  Lemma ba_le_respect_right : forall a b b',
      ba_equiv B b b' -> ba_le B a b -> ba_le B a b'.
  Proof.
    intros a b b' Hbb' Hab.
    pose proof (@ba_le_respects_equiv A B a a (ba_equiv_refl a)
      b b' Hbb') as Hproper.
    now apply (proj1 Hproper).
  Qed.

  Lemma ba_meet_top : forall a,
      ba_equiv B (ba_meet B a (ba_top B)) a.
  Proof.
    intro a. apply ba_le_antisymmetric.
    - apply ba_meet_le_left.
    - apply ba_le_meet; [apply ba_le_refl | apply ba_le_top].
  Qed.

  Lemma ba_top_meet : forall a,
      ba_equiv B (ba_meet B (ba_top B) a) a.
  Proof.
    intro a. eapply ba_equiv_trans.
    - apply ba_meet_commutative.
    - apply ba_meet_top.
  Qed.

  Lemma ba_join_bottom : forall a,
      ba_equiv B (ba_join B a (ba_bottom B)) a.
  Proof.
    intro a. apply ba_le_antisymmetric.
    - apply ba_join_le; [apply ba_le_refl | apply ba_bottom_le].
    - apply ba_le_join_left.
  Qed.

  Lemma ba_bottom_join : forall a,
      ba_equiv B (ba_join B (ba_bottom B) a) a.
  Proof.
    intro a. eapply ba_equiv_trans.
    - apply ba_join_commutative.
    - apply ba_join_bottom.
  Qed.

  Lemma ba_meet_imp_le : forall a b,
      ba_le B (ba_meet B (ba_imp B a b) a) b.
  Proof.
    intros a b. apply (proj2 (ba_imp_adjoint B (ba_imp B a b) a b)).
    apply ba_le_refl.
  Qed.

  Lemma ba_imp_top_of_le : forall a b,
      ba_le B a b -> ba_equiv B (ba_imp B a b) (ba_top B).
  Proof.
    intros a b Hab. apply ba_le_antisymmetric.
    - apply ba_le_top.
    - apply (proj1 (ba_imp_adjoint B (ba_top B) a b)).
      eapply ba_le_trans.
      + apply ba_meet_le_right.
      + exact Hab.
  Qed.

  Lemma ba_join_meet_compl_le_left : forall a b,
      ba_le B (ba_meet B (ba_join B a b) (ba_compl B b)) a.
  Proof.
    intros a b.
    eapply ba_le_respect_left.
    - apply ba_equiv_sym.
      eapply ba_equiv_trans with
        (b := ba_meet B (ba_compl B b) (ba_join B a b)).
      + apply ba_meet_commutative.
      + eapply ba_equiv_trans with
          (b := ba_join B (ba_meet B (ba_compl B b) a)
            (ba_meet B (ba_compl B b) b)).
        * apply ba_meet_join_distributive.
        * apply (@ba_join_respects_equiv A B).
          -- eapply ba_equiv_trans.
             ++ apply ba_meet_commutative.
             ++ apply ba_equiv_refl.
          -- eapply ba_equiv_trans.
             ++ apply ba_meet_commutative.
             ++ apply ba_meet_compl.
    - apply ba_join_le.
      + apply ba_meet_le_left.
      + apply ba_bottom_le.
  Qed.

  Lemma ba_compl_order_reflect : forall a b,
      ba_le B (ba_compl B b) (ba_compl B a) -> ba_le B a b.
  Proof.
    intros a b Hcompl.
    eapply ba_le_respect_right.
    - apply ba_compl_involutive.
    - eapply ba_le_respect_left.
      + apply ba_compl_involutive.
      + apply ba_compl_antitone. exact Hcompl.
  Qed.
End BooleanFacts.

(** * Normal Boolean modal algebras *)

Record modal_algebra (A : Type) := {
  modal_boolean : boolean_algebra A;
  modal_box : A -> A;
  modal_dia : A -> A;
  modal_box_respects_equiv :
    Proper (ba_equiv modal_boolean ==> ba_equiv modal_boolean) modal_box;
  modal_dia_respects_equiv :
    Proper (ba_equiv modal_boolean ==> ba_equiv modal_boolean) modal_dia;
  modal_box_top :
    ba_equiv modal_boolean (modal_box (ba_top modal_boolean))
      (ba_top modal_boolean);
  modal_box_meet : forall a b,
    ba_equiv modal_boolean (modal_box (ba_meet modal_boolean a b))
      (ba_meet modal_boolean (modal_box a) (modal_box b));
  modal_dia_dual : forall a,
    ba_equiv modal_boolean (modal_dia a)
      (ba_compl modal_boolean (modal_box (ba_compl modal_boolean a)))
}.

Arguments modal_boolean {A} _.
Arguments modal_box {A} _ _.
Arguments modal_dia {A} _ _.

Section ModalFacts.
  Context {A : Type} (M : modal_algebra A).
  Let B := modal_boolean M.

  Lemma box_monotone : forall a b,
      ba_le B a b -> ba_le B (modal_box M a) (modal_box M b).
  Proof.
    intros a b Hab.
    assert (Habmeet : ba_equiv B a (ba_meet B a b)).
    { apply ba_equiv_sym. apply ba_le_antisymmetric.
      - apply ba_meet_le_left.
      - apply ba_le_meet; [apply ba_le_refl | exact Hab]. }
    eapply ba_le_trans.
    - apply ba_equiv_implies_le.
      eapply ba_equiv_trans.
      + apply modal_box_respects_equiv. exact Habmeet.
      + apply modal_box_meet.
    - apply ba_meet_le_right.
  Qed.

  Lemma dual_box : forall a,
      ba_equiv B (modal_box M a)
        (ba_compl B (modal_dia M (ba_compl B a))).
  Proof.
    intro a. apply ba_equiv_sym.
    eapply ba_equiv_trans.
    - apply ba_compl_respects_equiv. apply modal_dia_dual.
    - eapply ba_equiv_trans.
      + apply ba_compl_involutive.
      + apply modal_box_respects_equiv. apply ba_compl_involutive.
  Qed.

  Lemma compl_box : forall a,
      ba_equiv B (ba_compl B (modal_box M a))
        (modal_dia M (ba_compl B a)).
  Proof.
    intro a. apply ba_equiv_sym.
    eapply ba_equiv_trans.
    - apply modal_dia_dual.
    - apply ba_compl_respects_equiv.
      apply modal_box_respects_equiv. apply ba_compl_involutive.
  Qed.

  Lemma compl_dia : forall a,
      ba_equiv B (ba_compl B (modal_dia M a))
        (modal_box M (ba_compl B a)).
  Proof.
    intro a. eapply ba_equiv_trans.
    - apply ba_compl_respects_equiv. apply modal_dia_dual.
    - apply ba_compl_involutive.
  Qed.

  Lemma dia_bot :
      ba_equiv B (modal_dia M (ba_bottom B)) (ba_bottom B).
  Proof.
    eapply ba_equiv_trans.
    - apply modal_dia_dual.
    - eapply ba_equiv_trans.
      + apply ba_compl_respects_equiv.
        apply modal_box_respects_equiv. apply ba_compl_bottom.
      + eapply ba_equiv_trans.
        * apply ba_compl_respects_equiv. apply modal_box_top.
        * apply ba_compl_top.
  Qed.

  Lemma box_imp_le_box_imp_box : forall a b,
      ba_le B (modal_box M (ba_imp B a b))
        (ba_imp B (modal_box M a) (modal_box M b)).
  Proof.
    intros a b.
    apply (proj1 (ba_imp_adjoint B
      (modal_box M (ba_imp B a b)) (modal_box M a) (modal_box M b))).
    eapply (@ba_le_respect_left A B
      (modal_box M (ba_meet B (ba_imp B a b) a))
      (ba_meet B (modal_box M (ba_imp B a b)) (modal_box M a))
      (modal_box M b)).
    - apply modal_box_meet.
    - apply box_monotone. apply ba_meet_imp_le.
  Qed.

  Lemma box_axiomK : forall a b,
      ba_equiv B
        (ba_imp B (modal_box M (ba_imp B a b))
          (ba_imp B (modal_box M a) (modal_box M b)))
        (ba_top B).
  Proof.
    intros a b. apply ba_imp_top_of_le. apply box_imp_le_box_imp_box.
  Qed.

  Lemma dia_or : forall a b,
      ba_equiv B (modal_dia M (ba_join B a b))
        (ba_join B (modal_dia M a) (modal_dia M b)).
  Proof.
    intros a b.
    eapply ba_equiv_trans.
    - apply modal_dia_dual.
    - eapply ba_equiv_trans.
      + apply ba_compl_respects_equiv.
        apply modal_box_respects_equiv. apply ba_de_morgan_join.
      + eapply ba_equiv_trans.
        * apply ba_compl_respects_equiv. apply modal_box_meet.
        * eapply ba_equiv_trans.
          -- apply ba_de_morgan_meet.
          -- apply ba_join_respects_equiv;
               apply ba_equiv_sym; apply modal_dia_dual.
  Qed.

  Lemma dia_monotone : forall a b,
      ba_le B a b -> ba_le B (modal_dia M a) (modal_dia M b).
  Proof.
    intros a b Hab.
    eapply ba_le_respect_left.
    - apply ba_equiv_sym. apply modal_dia_dual.
    - eapply ba_le_respect_right.
      + apply ba_equiv_sym. apply modal_dia_dual.
      + apply ba_compl_antitone. apply box_monotone.
        apply ba_compl_antitone. exact Hab.
  Qed.
End ModalFacts.

Record transitive_modal_algebra {A : Type} (M : modal_algebra A) := {
  modal_box_trans : forall a,
    ba_le (modal_boolean M) (modal_box M a) (modal_box M (modal_box M a))
}.

Record reflexive_modal_algebra {A : Type} (M : modal_algebra A) := {
  modal_box_refl : forall a,
    ba_le (modal_boolean M) (modal_box M a) a
}.

(** * Magari algebras *)

Record magari_algebra (A : Type) := {
  magari_modal : modal_algebra A;
  magari_box_diag : forall a,
    ba_equiv (modal_boolean magari_modal)
      (modal_box magari_modal
        (ba_imp (modal_boolean magari_modal) (modal_box magari_modal a) a))
      (modal_box magari_modal a)
}.

Arguments magari_modal {A} _.

Section MagariFacts.
  Context {A : Type} (G : magari_algebra A).
  Let M := magari_modal G.
  Let B := modal_boolean M.

  Lemma box_diag : forall a,
      ba_equiv B
        (modal_box M (ba_imp B (modal_box M a) a))
        (modal_box M a).
  Proof. apply magari_box_diag. Qed.

  Lemma dia_diag : forall a,
      ba_equiv B
        (modal_dia M (ba_meet B a (ba_compl B (modal_dia M a))))
        (modal_dia M a).
  Proof.
    intro a.
    eapply ba_equiv_trans with
      (b := ba_compl B (modal_box M
        (ba_compl B (ba_meet B a (ba_compl B (modal_dia M a)))))).
    - apply modal_dia_dual.
    - eapply ba_equiv_trans with
        (b := ba_compl B (modal_box M
          (ba_join B (ba_compl B a)
            (ba_compl B (ba_compl B (modal_dia M a)))))).
      + apply ba_compl_respects_equiv.
        apply modal_box_respects_equiv. apply ba_de_morgan_meet.
      + eapply ba_equiv_trans with
          (b := ba_compl B (modal_box M
            (ba_join B (ba_compl B a) (modal_dia M a)))).
        * apply ba_compl_respects_equiv.
          apply modal_box_respects_equiv.
          apply ba_join_respects_equiv.
          -- apply ba_equiv_refl.
          -- apply ba_compl_involutive.
        * eapply ba_equiv_trans with
            (b := ba_compl B (modal_box M
              (ba_join B (ba_compl B a)
                (ba_compl B (modal_box M (ba_compl B a)))))).
          -- apply ba_compl_respects_equiv.
             apply modal_box_respects_equiv.
             apply ba_join_respects_equiv.
             ++ apply ba_equiv_refl.
             ++ apply modal_dia_dual.
          -- eapply ba_equiv_trans with
              (b := ba_compl B (modal_box M
                (ba_join B (ba_compl B (modal_box M (ba_compl B a)))
                  (ba_compl B a)))).
             ++ apply ba_compl_respects_equiv.
                apply modal_box_respects_equiv.
                apply ba_join_commutative.
             ++ eapply ba_equiv_trans with
                 (b := ba_compl B (modal_box M
                   (ba_imp B (modal_box M (ba_compl B a))
                     (ba_compl B a)))).
                ** apply ba_compl_respects_equiv.
                   apply modal_box_respects_equiv.
                   apply ba_equiv_sym. apply ba_imp_definition.
                ** eapply ba_equiv_trans.
                   --- apply ba_compl_respects_equiv.
                       apply magari_box_diag.
                   --- apply ba_equiv_sym. apply modal_dia_dual.
  Qed.

  Lemma dia_trans : forall a,
      ba_le B (modal_dia M (modal_dia M a)) (modal_dia M a).
  Proof.
    intro a.
    set (d := modal_dia M a).
    set (dd := modal_dia M d).
    set (u := ba_join B a d).
    assert (Hd_u : ba_le B d (modal_dia M u)).
    { unfold u, d, dd.
      eapply ba_le_trans with
        (b := ba_join B (modal_dia M a) (modal_dia M (modal_dia M a))).
      - apply ba_le_join_left.
      - apply ba_equiv_implies_le.
        apply ba_equiv_sym. apply dia_or. }
    assert (Hdd_u : ba_le B dd (modal_dia M u)).
    { unfold u, d, dd.
      eapply ba_le_trans with
        (b := ba_join B (modal_dia M a) (modal_dia M (modal_dia M a))).
      - apply ba_le_join_right.
      - apply ba_equiv_implies_le.
        apply ba_equiv_sym. apply dia_or. }
    assert (Hinside :
      ba_le B (ba_meet B u (ba_compl B (modal_dia M u))) a).
    { eapply ba_le_trans with (b := ba_meet B u (ba_compl B d)).
      - apply ba_le_meet.
        + apply ba_meet_le_left.
        + eapply ba_le_trans.
          * apply ba_meet_le_right.
          * apply ba_compl_antitone. exact Hd_u.
      - unfold u. apply ba_join_meet_compl_le_left. }
    unfold dd, d.
    eapply ba_le_trans with (b := modal_dia M u).
    - exact Hdd_u.
    - eapply ba_le_trans with
        (b := modal_dia M
          (ba_meet B u (ba_compl B (modal_dia M u)))).
      + apply ba_equiv_implies_le. apply ba_equiv_sym. apply dia_diag.
      + apply dia_monotone. exact Hinside.
  Qed.

  Lemma box_trans : forall a,
      ba_le B (modal_box M a) (modal_box M (modal_box M a)).
  Proof.
    intro a.
    pose proof (dia_trans (ba_compl B a)) as Hdia.
    assert (Hleft :
      ba_equiv B
        (modal_dia M (modal_dia M (ba_compl B a)))
        (ba_compl B (modal_box M (modal_box M a)))).
    { eapply ba_equiv_trans.
      - apply modal_dia_respects_equiv.
        apply ba_equiv_sym. apply compl_box.
      - apply ba_equiv_sym. apply compl_box. }
    assert (Hright :
      ba_equiv B (modal_dia M (ba_compl B a))
        (ba_compl B (modal_box M a))).
    { apply ba_equiv_sym. apply compl_box. }
    apply ba_compl_order_reflect.
    eapply ba_le_respect_right.
    - exact Hright.
    - eapply ba_le_respect_left.
      + exact Hleft.
      + exact Hdia.
  Qed.

  Definition magari_transitive_modal_algebra : transitive_modal_algebra M.
  Proof. constructor. apply box_trans. Defined.
End MagariFacts.

(** * The complex algebra of a Kripke frame *)

Section ComplexBooleanAlgebra.
  Context (F : frame).

  Lemma world_set_equiv_is_equivalence :
      Equivalence (@world_set_equiv F).
  Proof.
    split.
    - exact (@world_set_equiv_refl F).
    - exact (@world_set_equiv_sym F).
    - exact (@world_set_equiv_trans F).
  Qed.

  Lemma world_set_included_is_preorder :
      PreOrder (@world_set_included F).
  Proof.
    split.
    - intros A x Hx. exact Hx.
    - intros A B C HAB HBC x Hx. apply HBC, HAB, Hx.
  Qed.

  Lemma world_set_included_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F ==> iff)
        (@world_set_included F).
  Proof.
    intros A A' HAA' B B' HBB'. split; intros H x Hx.
    - apply (proj1 (HBB' x)), H, (proj2 (HAA' x)), Hx.
    - apply (proj2 (HBB' x)), H, (proj1 (HAA' x)), Hx.
  Qed.

  Lemma world_set_intersection_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F ==>
        @world_set_equiv F) (@world_set_intersection F).
  Proof.
    intros A A' HAA' B B' HBB' x.
    specialize (HAA' x); specialize (HBB' x). firstorder.
  Qed.

  Lemma world_set_union_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F ==>
        @world_set_equiv F) (@world_set_union F).
  Proof.
    intros A A' HAA' B B' HBB' x.
    specialize (HAA' x); specialize (HBB' x). firstorder.
  Qed.

  Lemma world_set_complement_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F)
        (@world_set_complement F).
  Proof.
    intros A A' HAA' x. specialize (HAA' x). firstorder.
  Qed.

  Lemma world_set_implication_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F ==>
        @world_set_equiv F) (@world_set_implication F).
  Proof.
    intros A A' HAA' B B' HBB' x.
    specialize (HAA' x); specialize (HBB' x). firstorder.
  Qed.

  Lemma world_set_bottom_included : forall A : world_set F,
      world_set_included (@world_set_bottom F) A.
  Proof. firstorder. Qed.

  Lemma world_set_included_top : forall A : world_set F,
      world_set_included A (@world_set_top F).
  Proof. firstorder. Qed.

  Lemma world_set_intersection_included_left : forall A B : world_set F,
      world_set_included (world_set_intersection A B) A.
  Proof. firstorder. Qed.

  Lemma world_set_intersection_included_right : forall A B : world_set F,
      world_set_included (world_set_intersection A B) B.
  Proof. firstorder. Qed.

  Lemma world_set_included_intersection : forall A B C : world_set F,
      world_set_included A B -> world_set_included A C ->
      world_set_included A (world_set_intersection B C).
  Proof. firstorder. Qed.

  Lemma world_set_included_union_left : forall A B : world_set F,
      world_set_included A (world_set_union A B).
  Proof. firstorder. Qed.

  Lemma world_set_included_union_right : forall A B : world_set F,
      world_set_included B (world_set_union A B).
  Proof. firstorder. Qed.

  Lemma world_set_union_included : forall A B C : world_set F,
      world_set_included A C -> world_set_included B C ->
      world_set_included (world_set_union A B) C.
  Proof. firstorder. Qed.

  Lemma world_set_intersection_commutative : forall A B : world_set F,
      world_set_equiv (world_set_intersection A B)
        (world_set_intersection B A).
  Proof. firstorder. Qed.

  Lemma world_set_union_commutative : forall A B : world_set F,
      world_set_equiv (world_set_union A B) (world_set_union B A).
  Proof. firstorder. Qed.

  Lemma world_set_intersection_union_distributive :
      forall A B C : world_set F,
        world_set_equiv (world_set_intersection A (world_set_union B C))
          (world_set_union (world_set_intersection A B)
            (world_set_intersection A C)).
  Proof. firstorder. Qed.

  Lemma world_set_complement_involutive : forall A : world_set F,
      world_set_equiv (world_set_complement (world_set_complement A)) A.
  Proof.
    intros A x. unfold world_set_complement.
    destruct (classic (A x)); tauto.
  Qed.

  Lemma world_set_complement_antitone : forall A B : world_set F,
      world_set_included A B ->
      world_set_included (world_set_complement B)
        (world_set_complement A).
  Proof. firstorder. Qed.

  Lemma world_set_complement_top :
      world_set_equiv (world_set_complement (@world_set_top F))
        (@world_set_bottom F).
  Proof. firstorder. Qed.

  Lemma world_set_complement_bottom :
      world_set_equiv (world_set_complement (@world_set_bottom F))
        (@world_set_top F).
  Proof. firstorder. Qed.

  Lemma world_set_intersection_complement : forall A : world_set F,
      world_set_equiv (world_set_intersection A (world_set_complement A))
        (@world_set_bottom F).
  Proof. firstorder. Qed.

  Lemma world_set_union_complement : forall A : world_set F,
      world_set_equiv (world_set_union A (world_set_complement A))
        (@world_set_top F).
  Proof.
    intros A x. unfold world_set_union, world_set_complement, world_set_top.
    destruct (classic (A x)); tauto.
  Qed.

  Lemma world_set_de_morgan_intersection : forall A B : world_set F,
      world_set_equiv
        (world_set_complement (world_set_intersection A B))
        (world_set_union (world_set_complement A) (world_set_complement B)).
  Proof.
    intros A B x.
    unfold world_set_complement, world_set_intersection, world_set_union.
    destruct (classic (A x)); destruct (classic (B x)); tauto.
  Qed.

  Lemma world_set_de_morgan_union : forall A B : world_set F,
      world_set_equiv (world_set_complement (world_set_union A B))
        (world_set_intersection
          (world_set_complement A) (world_set_complement B)).
  Proof. firstorder. Qed.

  Lemma world_set_implication_definition : forall A B : world_set F,
      world_set_equiv (world_set_implication A B)
        (world_set_union (world_set_complement A) B).
  Proof.
    intros A B x.
    unfold world_set_implication, world_set_union, world_set_complement.
    destruct (classic (A x)); destruct (classic (B x)); tauto.
  Qed.

  Lemma world_set_implication_adjoint : forall X A B : world_set F,
      world_set_included (world_set_intersection X A) B <->
      world_set_included X (world_set_implication A B).
  Proof. firstorder. Qed.

  Definition complex_boolean_algebra : boolean_algebra (world_set F) :=
    {| ba_equiv := @world_set_equiv F;
       ba_le := @world_set_included F;
       ba_top := @world_set_top F;
       ba_bottom := @world_set_bottom F;
       ba_meet := @world_set_intersection F;
       ba_join := @world_set_union F;
       ba_compl := @world_set_complement F;
       ba_imp := @world_set_implication F;
       ba_equiv_is_equivalence := world_set_equiv_is_equivalence;
       ba_le_is_preorder := world_set_included_is_preorder;
       ba_le_antisymmetric := @world_set_equiv_antisymmetry F;
       ba_le_respects_equiv := world_set_included_respects_equiv;
       ba_meet_respects_equiv := world_set_intersection_respects_equiv;
       ba_join_respects_equiv := world_set_union_respects_equiv;
       ba_compl_respects_equiv := world_set_complement_respects_equiv;
       ba_imp_respects_equiv := world_set_implication_respects_equiv;
       ba_bottom_le := world_set_bottom_included;
       ba_le_top := world_set_included_top;
       ba_meet_le_left := world_set_intersection_included_left;
       ba_meet_le_right := world_set_intersection_included_right;
       ba_le_meet := world_set_included_intersection;
       ba_le_join_left := world_set_included_union_left;
       ba_le_join_right := world_set_included_union_right;
       ba_join_le := world_set_union_included;
       ba_meet_commutative := world_set_intersection_commutative;
       ba_join_commutative := world_set_union_commutative;
       ba_meet_join_distributive :=
         world_set_intersection_union_distributive;
       ba_compl_involutive := world_set_complement_involutive;
       ba_compl_antitone := world_set_complement_antitone;
       ba_compl_top := world_set_complement_top;
       ba_compl_bottom := world_set_complement_bottom;
       ba_meet_compl := world_set_intersection_complement;
       ba_join_compl := world_set_union_complement;
       ba_de_morgan_meet := world_set_de_morgan_intersection;
       ba_de_morgan_join := world_set_de_morgan_union;
       ba_imp_definition := world_set_implication_definition;
       ba_imp_adjoint := world_set_implication_adjoint |}.

  Lemma complex_box_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F) (@complex_box F).
  Proof.
    intros A B HAB x. split; intros Hbox y Rxy.
    - apply (proj1 (HAB y)), Hbox, Rxy.
    - apply (proj2 (HAB y)), Hbox, Rxy.
  Qed.

  Lemma complex_dia_respects_equiv :
      Proper (@world_set_equiv F ==> @world_set_equiv F) (@complex_dia F).
  Proof.
    intros A B HAB x. split; intros [y [Rxy Hy]]; exists y; split.
    - exact Rxy.
    - apply (proj1 (HAB y)), Hy.
    - exact Rxy.
    - apply (proj2 (HAB y)), Hy.
  Qed.

  Definition complex_modal_algebra : modal_algebra (world_set F).
  Proof.
    refine
      {| modal_boolean := complex_boolean_algebra;
         modal_box := @complex_box F;
         modal_dia := @complex_dia F |}.
    - exact complex_box_respects_equiv.
    - exact complex_dia_respects_equiv.
    - exact (@complex_box_top F).
    - exact (@complex_box_intersection F).
    - exact (@complex_dia_dual F).
  Defined.

  Lemma complex_boolean_order_iff : forall A B : world_set F,
      ba_le complex_boolean_algebra A B <-> world_set_included A B.
  Proof. reflexivity. Qed.

  Lemma complex_boolean_equiv_iff : forall A B : world_set F,
      ba_equiv complex_boolean_algebra A B <-> world_set_equiv A B.
  Proof. reflexivity. Qed.
End ComplexBooleanAlgebra.
