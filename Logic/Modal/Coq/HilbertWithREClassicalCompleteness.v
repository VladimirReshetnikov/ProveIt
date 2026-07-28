(**
  Classical completeness of the raw WithRE propositional basis.

  [with_re_proves] deliberately has only Foundation's six constructors:
  substituted raw axioms, modus ponens, replacement of equivalents, and
  the Lukasiewicz K/S/EC basis.  This file proves that its empty-axiom
  instance nevertheless contains every classical tautology.  No tautology
  or local-assumption constructor is added to the calculus.

  The proof reduces an arbitrary modal formula to a finite propositional
  skeleton over [nat].  Atomic formulas and whole boxed subformulas are the
  leaves of that skeleton.  Modal-K completeness supplies a proof of the
  skeleton; erasing every box occurring inside that proof eliminates the
  modal K and necessitation steps.  Finally, substitution decodes the finite
  skeleton back to the original formula.
*)

From Stdlib Require Import Lists.List Logic.ClassicalDescription.
From FoundationModal Require Import
  Syntax HilbertK LogicInfrastructure EntailmentExtensions
  HilbertWithRE CanonicalK.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition with_re_empty_axioms {AtomType : Type}
    : with_re_axiom AtomType :=
  fun _ => False.

(** Replace every boxed subformula by [Top].  This is used on a modal-K
    derivation, not on the target tautology itself. *)
Fixpoint with_re_erase_boxes {AtomType : Type} (p : formula AtomType)
    : formula AtomType :=
  match p with
  | Atom a => Atom a
  | Bottom => Bottom
  | Imp q r => Imp (with_re_erase_boxes q) (with_re_erase_boxes r)
  | Box _ => Top
  end.

Lemma with_re_empty_identity :
  forall (AtomType : Type) (p : formula AtomType),
    with_re_proves (@with_re_empty_axioms AtomType) (Imp p p).
Proof.
  intros AtomType p.
  eapply WRE_mp.
  - eapply WRE_mp.
    + exact (WRE_imply_S p (Imp p p) p).
    + exact (WRE_imply_K p (Imp p p)).
  - exact (WRE_imply_K p p).
Qed.

Lemma with_re_empty_top :
  forall AtomType : Type,
    with_re_proves (@with_re_empty_axioms AtomType) Top.
Proof.
  intro AtomType. exact (with_re_empty_identity Bottom).
Qed.

(** A modal-K proof becomes a raw empty-WithRE proof after boxes are erased.
    Modal K erases to [Top -> Top -> Top], an instance of propositional K;
    necessitation erases to [Top]. *)
Lemma K_proves_erase_boxes_with_re :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves p ->
    with_re_proves (@with_re_empty_axioms AtomType)
      (with_re_erase_boxes p).
Proof.
  intros AtomType p Hp; induction Hp; simpl.
  - apply WRE_imply_K.
  - apply WRE_imply_S.
  - apply WRE_elim_contra.
  - exact (WRE_imply_K Top Top).
  - exact (WRE_mp IHHp1 IHHp2).
  - apply with_re_empty_top.
Qed.

(** Empty-WithRE proofs may change atom types.  The general WithRE
    substitution theorem keeps a fixed atom type because a raw axiom
    predicate is fixed there.  For the empty predicate the raw-axiom case is
    impossible, so this stronger transport is available. *)
Lemma with_re_empty_substitute_between :
  forall (A B : Type) (sigma : A -> formula B) p,
    with_re_proves (@with_re_empty_axioms A) p ->
    with_re_proves (@with_re_empty_axioms B) (substitute sigma p).
Proof.
  intros A B sigma p Hp; induction Hp.
  - contradiction.
  - simpl. exact (WRE_mp IHHp1 IHHp2).
  - change
      (with_re_proves (@with_re_empty_axioms B)
        (Iff (Box (substitute sigma p)) (Box (substitute sigma q)))).
    apply WRE_re.
    change
      (with_re_proves (@with_re_empty_axioms B)
        (Iff (substitute sigma p) (substitute sigma q))) in IHHp.
    exact IHHp.
  - change
      (with_re_proves (@with_re_empty_axioms B)
        (Hilbert_imply_K (substitute sigma p) (substitute sigma q))).
    apply WRE_imply_K.
  - change
      (with_re_proves (@with_re_empty_axioms B)
        (Hilbert_imply_S (substitute sigma p) (substitute sigma q)
          (substitute sigma r))).
    apply WRE_imply_S.
  - change
      (with_re_proves (@with_re_empty_axioms B)
        (Hilbert_elim_contra (substitute sigma p) (substitute sigma q))).
    apply WRE_elim_contra.
Qed.

(** The propositional leaves of a modal formula.  Boxes are intentionally
    opaque leaves, matching [classical_eval]. *)
Fixpoint with_re_propositional_support {AtomType : Type}
    (p : formula AtomType) : list (formula AtomType) :=
  match p with
  | Atom a => [Atom a]
  | Bottom => []
  | Imp q r =>
      with_re_propositional_support q ++
      with_re_propositional_support r
  | Box q => [Box q]
  end.

(** Classical informative equality is needed only to number the finitely
    many leaves of one target formula. *)
Definition with_re_classical_eq_dec (X : Type) (x y : X)
    : {x = y} + {x <> y} :=
  excluded_middle_informative (x = y).

Fixpoint with_re_support_index {X : Type} (x : X) (xs : list X) : nat :=
  match xs with
  | [] => 0
  | y :: ys =>
      if with_re_classical_eq_dec x y
      then 0
      else S (with_re_support_index x ys)
  end.

Lemma with_re_nth_support_index :
  forall (X : Type) (x d : X) xs,
    In x xs ->
    nth (with_re_support_index x xs) xs d = x.
Proof.
  intros X x d xs; induction xs as [|y ys IH]; intro Hin.
  - contradiction.
  - simpl in Hin |- *.
    destruct (with_re_classical_eq_dec x y) as [Heq | Hne].
    + now subst y.
    + simpl. apply IH. destruct Hin as [Heq | Hin].
      * subst y. now exfalso.
      * exact Hin.
Qed.

(** The box-free natural-number skeleton determined by a finite support. *)
Fixpoint with_re_propositional_skeleton {AtomType : Type}
    (support : list (formula AtomType)) (p : formula AtomType)
    : formula nat :=
  match p with
  | Atom a => Atom (with_re_support_index (Atom a) support)
  | Bottom => Bottom
  | Imp q r =>
      Imp (with_re_propositional_skeleton support q)
          (with_re_propositional_skeleton support r)
  | Box q => Atom (with_re_support_index (Box q) support)
  end.

Definition with_re_support_decode {AtomType : Type}
    (support : list (formula AtomType)) (n : nat) : formula AtomType :=
  nth n support Bottom.

Lemma with_re_skeleton_classical_eval :
  forall (AtomType : Type) (support : list (formula AtomType))
         (rho : formula nat -> Prop) p,
    classical_eval rho (with_re_propositional_skeleton support p) <->
    classical_eval
      (fun q => classical_eval rho
        (with_re_propositional_skeleton support q)) p.
Proof.
  intros AtomType support rho p; induction p; simpl; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Lemma with_re_skeleton_tautology :
  forall (AtomType : Type) (support : list (formula AtomType)) p,
    classical_tautology p ->
    classical_tautology (with_re_propositional_skeleton support p).
Proof.
  intros AtomType support p Htaut rho.
  apply (proj2 (with_re_skeleton_classical_eval support rho p)).
  apply Htaut.
Qed.

Lemma with_re_erase_skeleton :
  forall (AtomType : Type) (support : list (formula AtomType)) p,
    with_re_erase_boxes (with_re_propositional_skeleton support p) =
    with_re_propositional_skeleton support p.
Proof.
  intros AtomType support p; induction p; simpl; try reflexivity.
  now rewrite IHp1, IHp2.
Qed.

Lemma with_re_decode_skeleton :
  forall (AtomType : Type) (support : list (formula AtomType)) p,
    (forall q, In q (with_re_propositional_support p) -> In q support) ->
    substitute (with_re_support_decode support)
      (with_re_propositional_skeleton support p) = p.
Proof.
  intros AtomType support p; induction p as [a | | p IHp q IHq | p IHp];
    intro Hsupport; simpl in *.
  - unfold with_re_support_decode.
    apply with_re_nth_support_index, Hsupport; now left.
  - reflexivity.
  - f_equal.
    + apply IHp. intros r Hr. apply Hsupport, in_or_app; now left.
    + apply IHq. intros r Hr. apply Hsupport, in_or_app; now right.
  - unfold with_re_support_decode.
    apply with_re_nth_support_index, Hsupport; now left.
Qed.

Lemma with_re_decode_own_skeleton :
  forall (AtomType : Type) (p : formula AtomType),
    substitute
      (with_re_support_decode (with_re_propositional_support p))
      (with_re_propositional_skeleton
        (with_re_propositional_support p) p) = p.
Proof.
  intros AtomType p. apply with_re_decode_skeleton. auto.
Qed.

(** The promised gap-closing theorem: K/S/EC and modus ponens already prove
    every classical tautology, uniformly over the atom type and with boxes
    treated propositionally. *)
Theorem with_re_empty_classical_complete :
  forall AtomType : Type,
    with_re_classical_complete
      (fun _ : formula AtomType => False).
Proof.
  intros AtomType p Htaut.
  set (support := with_re_propositional_support p).
  set (skeleton := with_re_propositional_skeleton support p).
  assert (Hskeleton_taut : classical_tautology skeleton).
  { subst skeleton. now apply with_re_skeleton_tautology. }
  assert (Hskeleton_K : K_proves skeleton).
  { apply K_complete, classical_tautology_valid. exact Hskeleton_taut. }
  pose proof (K_proves_erase_boxes_with_re Hskeleton_K) as Hwith_re.
  assert (Herase : with_re_erase_boxes skeleton = skeleton).
  { subst skeleton. apply with_re_erase_skeleton. }
  rewrite Herase in Hwith_re.
  pose proof
    (with_re_empty_substitute_between
      (with_re_support_decode support) Hwith_re) as Hdecoded.
  subst skeleton support.
  now rewrite with_re_decode_own_skeleton in Hdecoded.
Qed.

(** Weakening adds arbitrary raw modal axioms without affecting the
    propositional completeness proof. *)
Corollary with_re_classical_complete_weaken :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    with_re_classical_complete Ax.
Proof.
  intros AtomType Ax p Htaut.
  eapply
    (@with_re_weaker_of_subset_axioms AtomType
      (@with_re_empty_axioms AtomType) Ax).
  - intros q Hempty. contradiction.
  - now apply with_re_empty_classical_complete.
Qed.

Corollary with_re_classical_logic_from_basis :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    classical_logic (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax. apply with_re_classical_logic.
  apply with_re_classical_complete_weaken.
Qed.

Corollary with_re_e_entailment_from_basis :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    e_entailment (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax. apply with_re_e_entailment.
  apply with_re_classical_complete_weaken.
Qed.
