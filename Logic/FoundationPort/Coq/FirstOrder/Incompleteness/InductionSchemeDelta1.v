(**
  Structural bookkeeping used by the Delta-one induction-scheme recognizer.

  Raising the bound-variable level of syntax with [rew_cast_le] preserves
  both its structural Goedel code and its free-variable support.  The source
  states support preservation as finite-set equality; exact equality of the
  duplicate-tolerant lists is stronger and avoids decidable equality.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Coding.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The upper free-variable bound is attained whenever the list is nonempty.
    This list-level fact exposes the only combinatorics needed by the formula
    theorem below. *)
Lemma nat_free_bound_pred_in : forall xs,
  0 < nat_free_bound xs ->
  In (nat_free_bound xs - 1) xs.
Proof.
  induction xs as [|x xs IH].
  - simpl. lia.
  - intro H.
    change (0 < Nat.max (S x) (nat_free_bound xs)) in H.
    change (In (Nat.max (S x) (nat_free_bound xs) - 1) (x :: xs)).
    destruct (Nat.max_dec (S x) (nat_free_bound xs)) as [Hmax | Hmax].
    + rewrite Hmax. left. lia.
    + rewrite Hmax in H |- *. right. now apply IH.
Qed.

(** Source theorem [Semiformula.fvar?_fvSup_pred]. *)
Theorem semiformula_free_occurs_free_bound_pred : forall L n
    (p : semiproposition L n),
  0 < semiformula_free_bound p ->
  semiformula_free_occurs (semiformula_free_bound p - 1) p.
Proof.
  intros L n p Hpositive.
  apply (proj1 (semiformula_free_variable_list_spec p
    (semiformula_free_bound p - 1))).
  unfold semiformula_free_bound.
  now apply nat_free_bound_pred_in.
Qed.

(** Pointwise congruence for finite-vector codes.  Unlike equality of the
    underlying functions, this computational observation is constructive. *)
Lemma fin_nat_code_pointwise : forall k (v w : Fin.t k -> nat),
  (forall i, v i = w i) -> fin_nat_code v = fin_nat_code w.
Proof.
  induction k as [|k IH]; intros v w H; cbn [fin_nat_code].
  - reflexivity.
  - rewrite (H Fin.F1).
    rewrite (IH (fun i => v (Fin.FS i)) (fun i => w (Fin.FS i))
      (fun i => H (Fin.FS i))).
    reflexivity.
Qed.

(** Source theorem [Semiterm.quote_castLE], generalized from the source's
    arithmetic-model quotation to every verified language/free-variable
    encoding. *)
Theorem semiterm_code_rew_cast_le : forall L X n m
    (EL : language_encodable L) (EX : encoding X)
    (h : n <= m) (t : semiterm L X n),
  semiterm_code EL EX (rew_apply (@rew_cast_le L X n m h) t) =
  semiterm_code EL EX t.
Proof.
  intros L X n m EL EX h t.
  induction t as [i | x | k f v IH].
  - rewrite rew_cast_le_bvar, !semiterm_code_bvar, fin_value_cast_le.
    reflexivity.
  - rewrite rew_cast_le_fvar. reflexivity.
  - rewrite rew_apply_func, !semiterm_code_func.
    apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal.
    apply fin_nat_code_pointwise. intro i. apply IH.
Qed.

(** Source theorem [Semiterm.freeVariables_castLE], strengthened from set
    equality to exact list equality. *)
Theorem semiterm_free_variable_list_rew_cast_le : forall L X n m
    (h : n <= m) (t : semiterm L X n),
  semiterm_free_variable_list (rew_apply (@rew_cast_le L X n m h) t) =
  semiterm_free_variable_list t.
Proof.
  intros L X n m h t.
  induction t as [i | x | k f v IH].
  - rewrite rew_cast_le_bvar. reflexivity.
  - rewrite rew_cast_le_fvar. reflexivity.
  - rewrite rew_apply_func. cbn [semiterm_free_variable_list].
    apply flat_map_ext. exact IH.
Qed.

(** Source theorem [Semiformula.quote_castLE], with the same encoding-level
    generalization as the semiterm result. *)
Theorem semiformula_code_rew_cast_le : forall L X n m
    (EL : language_encodable L) (EX : encoding X)
    (h : n <= m) (p : semiformula L X n),
  semiformula_code EL EX
      (semiformula_rewrite (@rew_cast_le L X n m h) p) =
  semiformula_code EL EX p.
Proof.
  intros L X n m EL EX h p. revert m h.
  induction p as [n | n | n k r v | n k r v |
      n p IHp q IHq | n p IHp q IHq | n p IHp | n p IHp];
    intros m h; cbn [semiformula_rewrite semiformula_code].
  - reflexivity.
  - reflexivity.
  - apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal.
    apply fin_nat_code_pointwise. intro i.
    apply semiterm_code_rew_cast_le.
  - apply f_equal. apply f_equal. apply f_equal. apply f_equal.
    apply f_equal. apply f_equal.
    apply fin_nat_code_pointwise. intro i.
    apply semiterm_code_rew_cast_le.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_cast_le L X n m h)) p =
      semiformula_rewrite
        (@rew_cast_le L X (S n) (S m) (le_n_S n m h)) p).
    { apply semiformula_rewrite_ext. apply rew_q_cast_le. }
    rewrite Hr. now rewrite IHp.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_cast_le L X n m h)) p =
      semiformula_rewrite
        (@rew_cast_le L X (S n) (S m) (le_n_S n m h)) p).
    { apply semiformula_rewrite_ext. apply rew_q_cast_le. }
    rewrite Hr. now rewrite IHp.
Qed.

(** Source theorem [Semiformula.freeVariables_castLE], again strengthened to
    exact list equality. *)
Theorem semiformula_free_variable_list_rew_cast_le : forall L X n m
    (h : n <= m) (p : semiformula L X n),
  semiformula_free_variable_list
      (semiformula_rewrite (@rew_cast_le L X n m h) p) =
  semiformula_free_variable_list p.
Proof.
  intros L X n m h p. revert m h.
  induction p as [n | n | n k r v | n k r v |
      n p IHp q IHq | n p IHp q IHq | n p IHp | n p IHp];
    intros m h; cbn [semiformula_rewrite semiformula_free_variable_list].
  - reflexivity.
  - reflexivity.
  - assert (Hfunctions :
        forall i, semiterm_free_variable_list
          (rew_apply (rew_cast_le h) (v i)) =
        semiterm_free_variable_list (v i)).
    { intro i. apply semiterm_free_variable_list_rew_cast_le. }
    apply flat_map_ext. exact Hfunctions.
  - assert (Hfunctions :
        forall i, semiterm_free_variable_list
          (rew_apply (rew_cast_le h) (v i)) =
        semiterm_free_variable_list (v i)).
    { intro i. apply semiterm_free_variable_list_rew_cast_le. }
    apply flat_map_ext. exact Hfunctions.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_cast_le L X n m h)) p =
      semiformula_rewrite
        (@rew_cast_le L X (S n) (S m) (le_n_S n m h)) p).
    { apply semiformula_rewrite_ext. apply rew_q_cast_le. }
    rewrite Hr. apply IHp.
  - assert (Hr :
      semiformula_rewrite
        (rew_q (@rew_cast_le L X n m h)) p =
      semiformula_rewrite
        (@rew_cast_le L X (S n) (S m) (le_n_S n m h)) p).
    { apply semiformula_rewrite_ext. apply rew_q_cast_le. }
    rewrite Hr. apply IHp.
Qed.

(** Pointwise source-style corollary, requiring no equality decision on the
    free-variable type. *)
Corollary semiformula_free_occurs_rew_cast_le : forall L X n m
    (h : n <= m) (p : semiformula L X n) x,
  semiformula_free_occurs x
      (semiformula_rewrite (@rew_cast_le L X n m h) p) <->
  semiformula_free_occurs x p.
Proof.
  intros L X n m h p x.
  rewrite <- !semiformula_free_variable_list_spec.
  now rewrite semiformula_free_variable_list_rew_cast_le.
Qed.
