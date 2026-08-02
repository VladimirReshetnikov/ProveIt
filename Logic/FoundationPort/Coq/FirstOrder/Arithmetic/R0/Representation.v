(**
  Recursive and syntactic representation over Cobham's arithmetic theory R0.

  This file ports the constructive representation layer of
  [Foundation/FirstOrder/Arithmetic/R0/Representation.lean].  The first
  result records that evaluation of every ordered-ring term in the standard
  natural-number model is primitive recursive.  Later sections build the
  arithmetic graph of a typed partial-recursive code on top of this lemma.
*)

From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality
  Vectors.Fin.
From Foundation.Vorspiel Require Import Arithmetic.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Model.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Arbitrary constants are primitive recursive even though the compact
    external basis exposes only zero and one as primitive constructors. *)
Lemma primitive_recursive1_constant : forall n c,
  primitive_recursive1 n (fun _ => c).
Proof.
  intros n c. induction c as [|c IH].
  - apply primitive_recursive1_zero.
  - replace (fun _ : Fin.t n -> nat => S c) with
      (fun v =>
        (fun w : Fin.t 2 -> nat =>
           w Fin.F1 + w (Fin.FS Fin.F1))
          (fun i => fin_two
            (fun _ : Fin.t n -> nat => c)
            (fun _ : Fin.t n -> nat => 1) i v)).
    + apply (@primitive_recursive1_comp n 2
        (fun w : Fin.t 2 -> nat =>
          w Fin.F1 + w (Fin.FS Fin.F1))
        (fun i => fin_two
          (fun _ : Fin.t n -> nat => c)
          (fun _ : Fin.t n -> nat => 1) i)).
      * apply primitive_recursive1_add.
      * intro i.
        refine (@Fin.caseS' 1 i
          (fun j => primitive_recursive1 n
            (fin_two
              (fun _ : Fin.t n -> nat => c)
              (fun _ : Fin.t n -> nat => 1) j)) _ _).
        -- exact IH.
        -- intro j.
           refine (@Fin.caseS' 0 j
             (fun q => primitive_recursive1 n
               (fin_two
                 (fun _ : Fin.t n -> nat => c)
                 (fun _ : Fin.t n -> nat => 1) (Fin.FS q))) _ _).
           ++ apply primitive_recursive1_one.
           ++ intros q. inversion q.
    + apply functional_extensionality. intro v.
      rewrite fin_two_first, fin_two_second, Nat.add_1_r. reflexivity.
Qed.

(** Binary composition is factored once for the addition and multiplication
    branches of term evaluation. *)
Lemma primitive_recursive1_compose_binary : forall n
    (op : nat -> nat -> nat)
    (f g : (Fin.t n -> nat) -> nat),
  primitive_recursive1 2
    (fun v => op (v Fin.F1) (v (Fin.FS Fin.F1))) ->
  primitive_recursive1 n f ->
  primitive_recursive1 n g ->
  primitive_recursive1 n (fun v => op (f v) (g v)).
Proof.
  intros n op f g Hop Hf Hg.
  replace (fun v => op (f v) (g v)) with
      (fun v =>
        (fun w : Fin.t 2 -> nat =>
           op (w Fin.F1) (w (Fin.FS Fin.F1)))
          (fun i => fin_two f g i v)).
  - apply (@primitive_recursive1_comp n 2
      (fun w : Fin.t 2 -> nat =>
        op (w Fin.F1) (w (Fin.FS Fin.F1)))
      (fun i => fin_two f g i)).
    + exact Hop.
    + intro i.
      refine (@Fin.caseS' 1 i
        (fun j => primitive_recursive1 n (fin_two f g j)) _ _).
      * exact Hf.
      * intro j.
        refine (@Fin.caseS' 0 j
          (fun q => primitive_recursive1 n
            (fin_two f g (Fin.FS q))) _ _).
        -- exact Hg.
        -- intros q. inversion q.
  - apply functional_extensionality. intro v.
    now rewrite fin_two_first, fin_two_second.
Qed.

(** Source theorem [term_primrec].  Free variables are fixed parameters;
    the finite bound-variable environment is the recursive input vector. *)
Theorem r0_semiterm_primitive_recursive : forall X n
    (t : semiterm oring_language X n) (fv : X -> nat),
  primitive_recursive1 n
    (fun bv => semiterm_val nat_standard_structure bv fv t).
Proof.
  intros X n t. induction t as [i | x | k op args IH]; intro fv.
  - cbn [semiterm_val]. apply primitive_recursive1_proj.
  - cbn [semiterm_val]. apply primitive_recursive1_constant.
  - destruct op.
    + cbn [semiterm_val nat_standard_structure oring_standard_structure].
      apply primitive_recursive1_zero.
    + cbn [semiterm_val nat_standard_structure oring_standard_structure].
      apply primitive_recursive1_one.
    + cbn [semiterm_val nat_standard_structure oring_standard_structure].
      eapply primitive_recursive1_compose_binary.
      * apply primitive_recursive1_add.
      * apply IH.
      * apply IH.
    + cbn [semiterm_val nat_standard_structure oring_standard_structure].
      eapply primitive_recursive1_compose_binary.
      * apply primitive_recursive1_mul.
      * apply IH.
      * apply IH.
Qed.
