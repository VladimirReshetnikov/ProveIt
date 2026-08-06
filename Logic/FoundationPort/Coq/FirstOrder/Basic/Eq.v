(**
  Semantic equality axioms and congruence.

  This ports the central semantic layer of
  [Foundation/FirstOrder/Basic/Eq.lean].  Rather than tying the results to a
  particular syntactic presentation of the equality-axiom theory, the model
  laws are an explicit capability record.  This both generalizes the source
  lemmas and isolates the exact hypotheses needed by later quotient work.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Lists.List Vectors.Fin.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.FunctionalExtensionality.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Logic.ProofIrrelevance Logic.PropExtensionality.
From FoundationModal Require Import GenericLogicSymbol.
From Foundation.Vorspiel Require Import Matrix Quotient.
From Foundation.Vorspiel.Set Require Import Cofinite.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics ModelTheory Elementary RewriteClosure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

(** Total lookup in a finite vector, generalized from the source's implicit
    inhabited default to an explicit fallback value. *)
Definition matrix_iget {A k} (default : A)
    (v : Fin.t k -> A) (x : nat) : A :=
  match lt_dec x k with
  | left h => v (Fin.of_nat_lt h)
  | right _ => default
  end.

Lemma matrix_iget_in_range : forall A k (default : A)
    (v : Fin.t k -> A) x (h : x < k),
  matrix_iget default v x = v (Fin.of_nat_lt h).
Proof.
  intros. unfold matrix_iget.
  destruct (lt_dec x k) as [h' | Hnot]; [|contradiction].
  now rewrite (Fin.of_nat_ext h' h).
Qed.

Definition first_order_eqv {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) (a b : M) : Prop :=
  semiformula_operator_eval Str (fin_two a b)
    (semiformula_eq_operator Heq).

(** Exact semantic content of reflexivity, symmetry, transitivity, and the
    function/relation congruence axiom families. *)
Record first_order_models_equality_axioms {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) : Prop := {
  first_order_eqv_refl : forall a, first_order_eqv Str Heq a a;
  first_order_eqv_symm : forall a b,
    first_order_eqv Str Heq a b -> first_order_eqv Str Heq b a;
  first_order_eqv_trans : forall a b c,
    first_order_eqv Str Heq a b ->
    first_order_eqv Str Heq b c ->
    first_order_eqv Str Heq a c;
  first_order_eqv_func_ext : forall k (F : language_func L k)
    (v w : Fin.t k -> M),
    (forall i, first_order_eqv Str Heq (v i) (w i)) ->
    first_order_eqv Str Heq
      (structure_func Str F v) (structure_func Str F w);
  first_order_eqv_rel_ext : forall k (R : language_rel L k)
    (v w : Fin.t k -> M),
    (forall i, first_order_eqv Str Heq (v i) (w i)) ->
    (structure_rel Str R v <-> structure_rel Str R w)
}.

Arguments first_order_eqv_refl {L M Str Heq} _ _.
Arguments first_order_eqv_symm {L M Str Heq} _ _ _ _.
Arguments first_order_eqv_trans {L M Str Heq} _ _ _ _ _ _.
Arguments first_order_eqv_func_ext {L M Str Heq} _ {k} _ _ _ _.
Arguments first_order_eqv_rel_ext {L M Str Heq} _ {k} _ _ _ _.

Lemma first_order_eqv_equivalence : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  first_order_models_equality_axioms Str Heq ->
  Equivalence (first_order_eqv Str Heq).
Proof.
  intros L M Str Heq H. constructor.
  - exact (first_order_eqv_refl H).
  - exact (first_order_eqv_symm H).
  - exact (first_order_eqv_trans H).
Qed.

Lemma first_order_eqv_rel_ext_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    k (R : language_rel L k) (v w : Fin.t k -> M),
  (forall i, first_order_eqv Str Heq (v i) (w i)) ->
  (structure_rel Str R v <-> structure_rel Str R w).
Proof. intros. now apply (first_order_eqv_rel_ext H). Qed.

(** A structure interpreting the chosen equality operator as Coq equality
    automatically validates every equality axiom. *)
Definition first_order_models_equality_axioms_of_interprets_eq
    {L M} (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq Str Heq) :
    first_order_models_equality_axioms Str Heq.
Proof.
  constructor.
  - intro a. unfold first_order_eqv.
    apply (proj2 (structure_eq_operator Hstd a a)). reflexivity.
  - intros a b Hab. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd b a)). symmetry.
    now apply (proj1 (structure_eq_operator Hstd a b)).
  - intros a b c Hab Hbc. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd a c)).
    transitivity b.
    + now apply (proj1 (structure_eq_operator Hstd a b)).
    + now apply (proj1 (structure_eq_operator Hstd b c)).
  - intros k F v w Hvw. unfold first_order_eqv in *.
    apply (proj2 (structure_eq_operator Hstd
      (structure_func Str F v) (structure_func Str F w))).
    f_equal. apply functional_extensionality. intro i.
    now apply (proj1 (structure_eq_operator Hstd (v i) (w i))).
  - intros k R v w Hvw.
    assert (Henv : v = w).
    { apply functional_extensionality. intro i.
      unfold first_order_eqv in Hvw.
      now apply (proj1 (structure_eq_operator Hstd (v i) (w i))). }
    now subst w.
Defined.

Lemma first_order_eqv_fin_env_cons : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    n (a a' : M) (b b' : Fin.t n -> M),
  first_order_eqv Str Heq a a' ->
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  forall i, first_order_eqv Str Heq
    (fin_env_cons a b i) (fin_env_cons a' b' i).
Proof.
  intros L M Str Heq H n a a' b b' Ha Hb i.
  refine (@Fin.caseS' n i (fun j => first_order_eqv Str Heq
    (fin_env_cons a b j) (fin_env_cons a' b' j)) Ha _).
  exact Hb.
Qed.

(** Every term respects equality-equivalent bound and free environments. *)
Theorem semiterm_val_eqv : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b b' : Fin.t n -> M) (f f' : X -> M)
    (t : semiterm L X n),
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  (forall x, first_order_eqv Str Heq (f x) (f' x)) ->
  first_order_eqv Str Heq
    (semiterm_val Str b f t) (semiterm_val Str b' f' t).
Proof.
  intros L M X n Str Heq H b b' f f' t Hb Hf.
  induction t as [i | x | k F v IH]; simpl.
  - exact (Hb i).
  - exact (Hf x).
  - apply (first_order_eqv_func_ext H). exact IH.
Qed.

(** Consequently every formula is invariant under pointwise
    equality-equivalent environments. *)
Theorem semiformula_eval_eqv : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (p : semiformula L X n) (b b' : Fin.t n -> M)
    (f f' : X -> M),
  (forall i, first_order_eqv Str Heq (b i) (b' i)) ->
  (forall x, first_order_eqv Str Heq (f x) (f' x)) ->
  (semiformula_eval Str b f p <-> semiformula_eval Str b' f' p).
Proof.
  intros L M X n Str Heq H p.
  induction p as [n0 | n0 | n0 k R v | n0 k R v |
    n0 p IHp q IHq | n0 p IHp q IHq | n0 p IHp | n0 p IHp];
    intros b b' f f' Hb Hf; simpl; try tauto.
  - apply (first_order_eqv_rel_ext H). intro i.
    exact (@semiterm_val_eqv L M X n0 Str Heq H
      b b' f f' (v i) Hb Hf).
  - pose proof (first_order_eqv_rel_ext H R
      (fun i => semiterm_val Str b f (v i))
      (fun i => semiterm_val Str b' f' (v i))) as Hrel.
    specialize (Hrel (fun i => @semiterm_val_eqv L M X n0 Str Heq H
      b b' f f' (v i) Hb Hf)). tauto.
  - rewrite (IHp b b' f f' Hb Hf), (IHq b b' f f' Hb Hf).
    tauto.
  - rewrite (IHp b b' f f' Hb Hf), (IHq b b' f f' Hb Hf).
    tauto.
  - split; intros Hall x.
    + apply (proj1 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)).
      exact (Hall x).
    + apply (proj2 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)).
      exact (Hall x).
  - split; intros Hex.
    + destruct Hex as [x Hx]. exists x.
      apply (proj1 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)). exact Hx.
    + destruct Hex as [x Hx]. exists x.
      apply (proj2 (IHp _ _ f f'
        (first_order_eqv_fin_env_cons H
          (first_order_eqv_refl H x) Hb) Hf)). exact Hx.
Qed.

(** * Concrete equality axioms *)

Definition first_order_eq_empty_bound_env {A} : Fin.t 0 -> A :=
  fun i => match i with end.

Definition first_order_eq_empty_free_env {A} : Empty_set -> A :=
  fun x => match x with end.

Definition first_order_eq_atom {L X n}
    (Heq : semiformula_has_eq_operator L)
    (t u : semiterm L X n) : semiformula L X n :=
  semiformula_operator_apply (semiformula_eq_operator Heq) (fin_two t u).

Definition first_order_eq_refl_sentence {L}
    (Heq : semiformula_has_eq_operator L) : sentence L :=
  first_all_closure (semiformula_universal_quantifier L Empty_set) 1
    (first_order_eq_atom Heq
      (@Semiterm_bvar L Empty_set 1 Fin.F1)
      (@Semiterm_bvar L Empty_set 1 Fin.F1)).

Definition first_order_eq_symm_sentence {L}
    (Heq : semiformula_has_eq_operator L) : sentence L :=
  first_all_closure (semiformula_universal_quantifier L Empty_set) 2
    (semiformula_imp
      (first_order_eq_atom Heq
        (@Semiterm_bvar L Empty_set 2 Fin.F1)
        (@Semiterm_bvar L Empty_set 2 (Fin.FS Fin.F1)))
      (first_order_eq_atom Heq
        (@Semiterm_bvar L Empty_set 2 (Fin.FS Fin.F1))
        (@Semiterm_bvar L Empty_set 2 Fin.F1))).

Definition first_order_eq_trans_sentence {L}
    (Heq : semiformula_has_eq_operator L) : sentence L :=
  first_all_closure (semiformula_universal_quantifier L Empty_set) 3
    (semiformula_imp
      (first_order_eq_atom Heq
        (@Semiterm_bvar L Empty_set 3 Fin.F1)
        (@Semiterm_bvar L Empty_set 3 (Fin.FS Fin.F1)))
      (semiformula_imp
        (first_order_eq_atom Heq
          (@Semiterm_bvar L Empty_set 3 (Fin.FS Fin.F1))
          (@Semiterm_bvar L Empty_set 3 (Fin.FS (Fin.FS Fin.F1))))
        (first_order_eq_atom Heq
          (@Semiterm_bvar L Empty_set 3 Fin.F1)
          (@Semiterm_bvar L Empty_set 3
            (Fin.FS (Fin.FS Fin.F1)))))).

Definition first_order_eq_pair_conjunction {L}
    (Heq : semiformula_has_eq_operator L) k :
    semisentence L (k + k) :=
  generic_matrix_conj (semiformula_connectives L Empty_set (k + k)) k
    (fun i => first_order_eq_atom Heq
      (@Semiterm_bvar L Empty_set (k + k) (Fin.L k i))
      (@Semiterm_bvar L Empty_set (k + k) (Fin.R k i))).

Definition first_order_eq_func_ext_sentence {L}
    (Heq : semiformula_has_eq_operator L) k
    (F : language_func L k) : sentence L :=
  first_all_closure (semiformula_universal_quantifier L Empty_set) (k + k)
    (semiformula_imp
      (first_order_eq_pair_conjunction Heq k)
      (first_order_eq_atom Heq
        (Semiterm_func F (fun i =>
          @Semiterm_bvar L Empty_set (k + k) (Fin.L k i)))
        (Semiterm_func F (fun i =>
          @Semiterm_bvar L Empty_set (k + k) (Fin.R k i))))).

Definition first_order_eq_rel_ext_sentence {L}
    (Heq : semiformula_has_eq_operator L) k
    (R : language_rel L k) : sentence L :=
  first_all_closure (semiformula_universal_quantifier L Empty_set) (k + k)
    (semiformula_imp
      (first_order_eq_pair_conjunction Heq k)
      (semiformula_imp
        (Semiformula_rel R (fun i =>
          @Semiterm_bvar L Empty_set (k + k) (Fin.L k i)))
        (Semiformula_rel R (fun i =>
          @Semiterm_bvar L Empty_set (k + k) (Fin.R k i))))).

Inductive first_order_equality_axiom (L : language)
    (Heq : semiformula_has_eq_operator L) : theory L :=
| FirstOrderEqRefl :
    @first_order_equality_axiom L Heq
      (first_order_eq_refl_sentence Heq)
| FirstOrderEqSymm :
    @first_order_equality_axiom L Heq
      (first_order_eq_symm_sentence Heq)
| FirstOrderEqTrans :
    @first_order_equality_axiom L Heq
      (first_order_eq_trans_sentence Heq)
| FirstOrderEqFuncExt : forall k (F : language_func L k),
    @first_order_equality_axiom L Heq
      (first_order_eq_func_ext_sentence Heq F)
| FirstOrderEqRelExt : forall k (R : language_rel L k),
    @first_order_equality_axiom L Heq
      (first_order_eq_rel_ext_sentence Heq R).

Definition first_order_equality_axiom_list {L}
    (Heq : semiformula_has_eq_operator L)
    (Hfinite : language_finite L) : list (sentence L) :=
  [first_order_eq_refl_sentence Heq;
   first_order_eq_symm_sentence Heq;
   first_order_eq_trans_sentence Heq] ++
  map (fun s =>
    match s with
    | existT _ k F => first_order_eq_func_ext_sentence Heq F
    end)
    (finite_cover_list (language_finite_func Hfinite)) ++
  map (fun s =>
    match s with
    | existT _ k R => first_order_eq_rel_ext_sentence Heq R
    end)
    (finite_cover_list (language_finite_rel Hfinite)).

Lemma first_order_equality_axiom_list_complete : forall L
    (Heq : semiformula_has_eq_operator L)
    (Hfinite : language_finite L) sigma,
  @first_order_equality_axiom L Heq sigma ->
  In sigma (first_order_equality_axiom_list Heq Hfinite).
Proof.
  intros L Heq Hfinite sigma Hsigma. destruct Hsigma; simpl.
  - auto.
  - auto.
  - auto.
  - right; right; right. apply in_or_app. left.
    apply in_map_iff. exists (existT _ k F). split.
    + reflexivity.
    + apply finite_cover_complete.
  - right; right; right. apply in_or_app. right.
    apply in_map_iff. exists (existT _ k R). split.
    + reflexivity.
    + apply finite_cover_complete.
Qed.

Theorem first_order_equality_axiom_finitely_covered : forall L
    (Heq : semiformula_has_eq_operator L),
  language_finite L ->
  set_finitely_covered (@first_order_equality_axiom L Heq).
Proof.
  intros L Heq Hfinite.
  exists (first_order_equality_axiom_list Heq Hfinite).
  intros sigma Hsigma.
  now apply first_order_equality_axiom_list_complete.
Qed.

Lemma first_order_eq_atom_eval : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (b : Fin.t n -> M) (f : X -> M)
    (t u : semiterm L X n),
  semiformula_eval Str b f (first_order_eq_atom Heq t u) <->
  first_order_eqv Str Heq
    (semiterm_val Str b f t) (semiterm_val Str b f u).
Proof.
  intros. unfold first_order_eq_atom.
  rewrite semiformula_eval_operator_apply.
  unfold first_order_eqv.
  assert (Hargs :
    (fun i => semiterm_val Str b f (fin_two t u i)) =
    fin_two (semiterm_val Str b f t) (semiterm_val Str b f u)).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      semiterm_val Str b f (fin_two t u j) =
      fin_two (semiterm_val Str b f t) (semiterm_val Str b f u) j)
      eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      semiterm_val Str b f (fin_two t u (Fin.FS q)) =
      fin_two (semiterm_val Str b f t) (semiterm_val Str b f u)
        (Fin.FS q)) eq_refl _).
    intros q; inversion q. }
  now rewrite Hargs.
Qed.

Lemma first_order_matrix_conj_eval : forall L M X n
    (Str : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) k
    (v : Fin.t k -> semiformula L X n),
  semiformula_eval Str b f
      (generic_matrix_conj (semiformula_connectives L X n) k v) <->
  forall i, semiformula_eval Str b f (v i).
Proof.
  intros L M X n Str b f k. induction k as [|k IH]; intro v; simpl.
  - split; [intros _ i; inversion i | intros _; exact I].
  - rewrite IH. split.
    + intros [Hhead Htail] i.
      refine (@Fin.caseS' k i
        (fun j => semiformula_eval Str b f (v j)) Hhead _).
      exact Htail.
    + intro Hall. split.
      * apply Hall.
      * intro i. apply Hall.
Qed.

Lemma first_order_eq_pair_conjunction_eval : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) k
    (e : Fin.t (k + k) -> M),
  semiformula_eval Str e first_order_eq_empty_free_env
      (first_order_eq_pair_conjunction Heq k) <->
  forall i, first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i)).
Proof.
  intros. unfold first_order_eq_pair_conjunction.
  rewrite first_order_matrix_conj_eval. split; intros Hall i.
  - specialize (Hall i). rewrite first_order_eq_atom_eval in Hall.
    simpl in Hall. exact Hall.
  - rewrite first_order_eq_atom_eval. simpl. apply Hall.
Qed.

Lemma first_order_eq_refl_realize_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  sentence_realize Str (first_order_eq_refl_sentence Heq) <->
  forall a, first_order_eqv Str Heq a a.
Proof.
  intros. unfold sentence_realize, formula_eval,
    first_order_eq_refl_sentence.
  rewrite semiformula_eval_all_closure. split; intros H a.
  - specialize (H (fin_one a)).
    apply (proj1 (@first_order_eq_atom_eval
      L M Empty_set 1 Str Heq (fin_one a)
      first_order_eq_empty_free_env _ _)) in H.
    exact H.
  - rewrite first_order_eq_atom_eval. simpl. apply H.
Qed.

Lemma first_order_eq_symm_realize_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  sentence_realize Str (first_order_eq_symm_sentence Heq) <->
  forall a b,
    first_order_eqv Str Heq a b -> first_order_eqv Str Heq b a.
Proof.
  intros. unfold sentence_realize, formula_eval,
    first_order_eq_symm_sentence.
  rewrite semiformula_eval_all_closure. split.
  - intros H a b Hab. specialize (H (fin_two a b)).
    rewrite semiformula_eval_imp,
      !first_order_eq_atom_eval in H. simpl in H.
    exact (H Hab).
  - intros H e. rewrite semiformula_eval_imp,
      !first_order_eq_atom_eval. simpl.
    apply H.
Qed.

Lemma first_order_eq_trans_realize_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  sentence_realize Str (first_order_eq_trans_sentence Heq) <->
  forall a b c,
    first_order_eqv Str Heq a b ->
    first_order_eqv Str Heq b c ->
    first_order_eqv Str Heq a c.
Proof.
  intros. unfold sentence_realize, formula_eval,
    first_order_eq_trans_sentence.
  rewrite semiformula_eval_all_closure. split.
  - intros H a b c Hab Hbc.
    specialize (H (matrix_vec_cons a (fin_two b c))).
    rewrite !semiformula_eval_imp,
      !first_order_eq_atom_eval in H. simpl in H.
    exact (H Hab Hbc).
  - intros H e. rewrite !semiformula_eval_imp,
      !first_order_eq_atom_eval. simpl.
    apply H.
Qed.

Lemma first_order_eq_func_ext_realize_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) k
    (F : language_func L k),
  sentence_realize Str (first_order_eq_func_ext_sentence Heq F) <->
  forall e : Fin.t (k + k) -> M,
    (forall i,
      first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i))) ->
    first_order_eqv Str Heq
      (structure_func Str F (fun i => e (Fin.L k i)))
      (structure_func Str F (fun i => e (Fin.R k i))).
Proof.
  intros. unfold sentence_realize, formula_eval,
    first_order_eq_func_ext_sentence.
  rewrite semiformula_eval_all_closure. split; intros H e.
  - specialize (H e). rewrite semiformula_eval_imp,
      first_order_eq_pair_conjunction_eval,
      first_order_eq_atom_eval in H.
    simpl in H. exact H.
  - rewrite semiformula_eval_imp,
      first_order_eq_pair_conjunction_eval,
      first_order_eq_atom_eval. simpl. apply H.
Qed.

Lemma first_order_eq_rel_ext_realize_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) k
    (R : language_rel L k),
  sentence_realize Str (first_order_eq_rel_ext_sentence Heq R) <->
  forall e : Fin.t (k + k) -> M,
    (forall i,
      first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i))) ->
    structure_rel Str R (fun i => e (Fin.L k i)) ->
    structure_rel Str R (fun i => e (Fin.R k i)).
Proof.
  intros. unfold sentence_realize, formula_eval,
    first_order_eq_rel_ext_sentence.
  rewrite semiformula_eval_all_closure. split; intros H e.
  - specialize (H e). rewrite !semiformula_eval_imp,
      first_order_eq_pair_conjunction_eval in H.
    simpl in H. exact H.
  - rewrite !semiformula_eval_imp,
      first_order_eq_pair_conjunction_eval. simpl. apply H.
Qed.

Definition first_order_structure_models_equality_theory {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L) : Prop :=
  forall sigma, @first_order_equality_axiom L Heq sigma ->
    sentence_realize Str sigma.

Theorem first_order_structure_models_equality_theory_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L),
  first_order_structure_models_equality_theory Str Heq <->
  first_order_models_equality_axioms Str Heq.
Proof.
  intros L M Str Heq. split.
  - intro Hmodels.
    assert (Hreflexive : forall a, first_order_eqv Str Heq a a).
    { apply (proj1 (first_order_eq_refl_realize_iff Str Heq)).
      apply Hmodels. constructor. }
    assert (Hsymmetric : forall a b,
      first_order_eqv Str Heq a b ->
      first_order_eqv Str Heq b a).
    { apply (proj1 (first_order_eq_symm_realize_iff Str Heq)).
      apply Hmodels. constructor. }
    assert (Htransitive : forall a b c,
      first_order_eqv Str Heq a b ->
      first_order_eqv Str Heq b c ->
      first_order_eqv Str Heq a c).
    { apply (proj1 (first_order_eq_trans_realize_iff Str Heq)).
      apply Hmodels. constructor. }
    constructor.
    + exact Hreflexive.
    + exact Hsymmetric.
    + exact Htransitive.
    + intros k F v w Hvw.
      pose proof (proj1 (first_order_eq_func_ext_realize_iff Str Heq F)
        (Hmodels _ (FirstOrderEqFuncExt Heq F))) as Hfunc.
      pose (e := @matrix_vec_append M k v k w).
      specialize (Hfunc e).
      assert (Hpairs : forall i,
        first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i))).
      { intro i. unfold e.
        rewrite matrix_vec_append_left, matrix_vec_append_right.
        apply Hvw. }
      specialize (Hfunc Hpairs).
      assert (Hleft : (fun i => e (Fin.L k i)) = v).
      { apply functional_extensionality. intro i.
        unfold e. apply matrix_vec_append_left. }
      assert (Hright : (fun i => e (Fin.R k i)) = w).
      { apply functional_extensionality. intro i.
        unfold e. apply matrix_vec_append_right. }
      now rewrite Hleft, Hright in Hfunc.
    + intros k R v w Hvw. split; intro Hrel.
      * pose proof (proj1 (first_order_eq_rel_ext_realize_iff Str Heq R)
          (Hmodels _ (FirstOrderEqRelExt Heq R))) as Hext.
        pose (e := @matrix_vec_append M k v k w).
        specialize (Hext e).
        assert (Hpairs : forall i,
          first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i))).
        { intro i. unfold e.
          rewrite matrix_vec_append_left, matrix_vec_append_right.
          apply Hvw. }
        specialize (Hext Hpairs).
        assert (Hleft : (fun i => e (Fin.L k i)) = v).
        { apply functional_extensionality. intro i.
          unfold e. apply matrix_vec_append_left. }
        assert (Hright : (fun i => e (Fin.R k i)) = w).
        { apply functional_extensionality. intro i.
          unfold e. apply matrix_vec_append_right. }
        rewrite Hleft, Hright in Hext. exact (Hext Hrel).
      * pose proof (proj1 (first_order_eq_rel_ext_realize_iff Str Heq R)
          (Hmodels _ (FirstOrderEqRelExt Heq R))) as Hext.
        pose (e := @matrix_vec_append M k w k v).
        specialize (Hext e).
        assert (Hpairs : forall i,
          first_order_eqv Str Heq (e (Fin.L k i)) (e (Fin.R k i))).
        { intro i. unfold e.
          rewrite matrix_vec_append_left, matrix_vec_append_right.
          apply Hsymmetric, Hvw. }
        specialize (Hext Hpairs).
        assert (Hleft : (fun i => e (Fin.L k i)) = w).
        { apply functional_extensionality. intro i.
          unfold e. apply matrix_vec_append_left. }
        assert (Hright : (fun i => e (Fin.R k i)) = v).
        { apply functional_extensionality. intro i.
          unfold e. apply matrix_vec_append_right. }
        rewrite Hleft, Hright in Hext. exact (Hext Hrel).
  - intros H sigma Hsigma. destruct Hsigma.
    + apply (proj2 (first_order_eq_refl_realize_iff Str Heq)).
      exact (first_order_eqv_refl H).
    + apply (proj2 (first_order_eq_symm_realize_iff Str Heq)).
      exact (first_order_eqv_symm H).
    + apply (proj2 (first_order_eq_trans_realize_iff Str Heq)).
      exact (first_order_eqv_trans H).
    + apply (proj2 (first_order_eq_func_ext_realize_iff Str Heq F)).
      intros e Hpairs. apply (first_order_eqv_func_ext H). exact Hpairs.
    + apply (proj2 (first_order_eq_rel_ext_realize_iff Str Heq R)).
      intros e Hpairs Hrel.
      apply (proj1 (first_order_eqv_rel_ext H R _ _ Hpairs)).
      exact Hrel.
Qed.

Theorem first_order_model_models_equality_theory_iff : forall L
    (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L),
  first_order_models_theory m (@first_order_equality_axiom L Heq) <->
  first_order_models_equality_axioms
    (first_order_model_structure m) Heq.
Proof.
  intros. rewrite first_order_models_theory_iff.
  apply first_order_structure_models_equality_theory_iff.
Qed.

Corollary first_order_model_models_equality_theory_of_interprets_eq :
  forall L (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L),
  structure_interprets_eq (first_order_model_structure m) Heq ->
  first_order_models_theory m (@first_order_equality_axiom L Heq).
Proof.
  intros L m Heq Hstandard.
  apply (proj2 (first_order_model_models_equality_theory_iff m Heq)).
  apply first_order_models_equality_axioms_of_interprets_eq.
  exact Hstandard.
Qed.

(** * Quotienting a model by semantic equality *)

Definition first_order_eq_quotient {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq) :
    @explicit_quotient M (first_order_eqv Str Heq) :=
  equivalence_class_quotient (first_order_eqv_equivalence H).

Definition first_order_eq_quotient_carrier {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq) : Type :=
  quotient_carrier (first_order_eq_quotient H).

Definition first_order_eq_quotient_structure {L M}
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq) :
    first_order_structure L (first_order_eq_quotient_carrier H).
Proof.
  pose (Q := first_order_eq_quotient H).
  refine {| structure_func := fun k F v =>
      @quotient_vec_lift M (first_order_eqv Str Heq) Q k
        (quotient_carrier Q)
        (fun w => quotient_mk Q (structure_func Str F w)) _ v;
    structure_rel := fun k R v =>
      @quotient_vec_lift M (first_order_eqv Str Heq) Q k Prop
        (fun w => structure_rel Str R w) _ v |}.
  - intros xs ys Hxy.
    apply (proj2 (equivalence_class_mk_eq_iff
      (first_order_eqv_equivalence H) _ _)).
    apply (first_order_eqv_func_ext H). exact Hxy.
  - intros xs ys Hxy. apply propositional_extensionality.
    apply (first_order_eqv_rel_ext H). exact Hxy.
Defined.

Lemma first_order_eq_quotient_func_mk : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    k (F : language_func L k) (v : Fin.t k -> M),
  structure_func (first_order_eq_quotient_structure H) F
      (quotient_vec_mk (first_order_eq_quotient H) v) =
  quotient_mk (first_order_eq_quotient H) (structure_func Str F v).
Proof.
  intros. unfold first_order_eq_quotient_structure.
  apply quotient_vec_lift_mk.
Qed.

Lemma first_order_eq_quotient_rel_mk : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    k (R : language_rel L k) (v : Fin.t k -> M),
  structure_rel (first_order_eq_quotient_structure H) R
      (quotient_vec_mk (first_order_eq_quotient H) v) <->
  structure_rel Str R v.
Proof.
  intros. unfold first_order_eq_quotient_structure. simpl.
  rewrite (@quotient_vec_lift_mk M (first_order_eqv Str Heq)
    (first_order_eq_quotient H) k Prop
    (fun w => structure_rel Str R w)
    (fun xs ys Hxy =>
      @propositional_extensionality
        (structure_rel Str R xs) (structure_rel Str R ys)
        (first_order_eqv_rel_ext H R xs ys Hxy)) v).
  reflexivity.
Qed.

Theorem first_order_eq_quotient_term_value : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n),
  semiterm_val (first_order_eq_quotient_structure H)
      (fun i => quotient_mk (first_order_eq_quotient H) (b i))
      (fun x => quotient_mk (first_order_eq_quotient H) (f x)) t =
  quotient_mk (first_order_eq_quotient H)
      (semiterm_val Str b f t).
Proof.
  intros L M X n Str Heq H b f t.
  induction t as [i | x | k F v IH].
  - reflexivity.
  - reflexivity.
  - change
      (structure_func (first_order_eq_quotient_structure H) F
        (fun i => semiterm_val (first_order_eq_quotient_structure H)
          (fun j => quotient_mk (first_order_eq_quotient H) (b j))
          (fun x => quotient_mk (first_order_eq_quotient H) (f x))
          (v i)) =
       quotient_mk (first_order_eq_quotient H)
         (structure_func Str F
           (fun i => semiterm_val Str b f (v i)))).
  assert (Hargs :
    (fun i => semiterm_val (first_order_eq_quotient_structure H)
      (fun j => quotient_mk (first_order_eq_quotient H) (b j))
      (fun x => quotient_mk (first_order_eq_quotient H) (f x)) (v i)) =
    quotient_vec_mk (first_order_eq_quotient H)
      (fun i => semiterm_val Str b f (v i))).
  { apply functional_extensionality. exact IH. }
  rewrite Hargs. apply first_order_eq_quotient_func_mk.
Qed.

Lemma first_order_eq_quotient_fin_env_cons : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    n (a : M) (b : Fin.t n -> M),
  (fun i => quotient_mk (first_order_eq_quotient H)
      (fin_env_cons a b i)) =
  fin_env_cons (quotient_mk (first_order_eq_quotient H) a)
    (fun i => quotient_mk (first_order_eq_quotient H) (b i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    quotient_mk (first_order_eq_quotient H) (fin_env_cons a b j) =
    fin_env_cons (quotient_mk (first_order_eq_quotient H) a)
      (fun u => quotient_mk (first_order_eq_quotient H) (b u)) j)
    eq_refl _).
  intro j. reflexivity.
Qed.

Theorem first_order_eq_quotient_formula_eval : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (p : semiformula L X n) (b : Fin.t n -> M) (f : X -> M),
  semiformula_eval (first_order_eq_quotient_structure H)
      (fun i => quotient_mk (first_order_eq_quotient H) (b i))
      (fun x => quotient_mk (first_order_eq_quotient H) (f x)) p <->
  semiformula_eval Str b f p.
Proof.
  intros L M X n Str Heq H p.
  induction p as [n0 | n0 | n0 k R v | n0 k R v |
    n0 p IHp q IHq | n0 p IHp q IHq | n0 p IHp | n0 p IHp];
    intros b f.
  - reflexivity.
  - reflexivity.
  - change
      (structure_rel (first_order_eq_quotient_structure H) R
        (fun i => semiterm_val (first_order_eq_quotient_structure H)
          (fun j => quotient_mk (first_order_eq_quotient H) (b j))
          (fun x => quotient_mk (first_order_eq_quotient H) (f x))
          (v i)) <->
       structure_rel Str R
        (fun i => semiterm_val Str b f (v i))).
    assert (Hargs :
      (fun i => semiterm_val (first_order_eq_quotient_structure H)
        (fun j => quotient_mk (first_order_eq_quotient H) (b j))
        (fun x => quotient_mk (first_order_eq_quotient H) (f x)) (v i)) =
      quotient_vec_mk (first_order_eq_quotient H)
        (fun i => semiterm_val Str b f (v i))).
    { apply functional_extensionality. intro i.
      apply first_order_eq_quotient_term_value. }
    rewrite Hargs. apply first_order_eq_quotient_rel_mk.
  - change
      (~ structure_rel (first_order_eq_quotient_structure H) R
        (fun i => semiterm_val (first_order_eq_quotient_structure H)
          (fun j => quotient_mk (first_order_eq_quotient H) (b j))
          (fun x => quotient_mk (first_order_eq_quotient H) (f x))
          (v i)) <->
       ~ structure_rel Str R
        (fun i => semiterm_val Str b f (v i))).
    assert (Hargs :
      (fun i => semiterm_val (first_order_eq_quotient_structure H)
        (fun j => quotient_mk (first_order_eq_quotient H) (b j))
        (fun x => quotient_mk (first_order_eq_quotient H) (f x)) (v i)) =
      quotient_vec_mk (first_order_eq_quotient H)
        (fun i => semiterm_val Str b f (v i))).
    { apply functional_extensionality. intro i.
      apply first_order_eq_quotient_term_value. }
    rewrite Hargs, first_order_eq_quotient_rel_mk. tauto.
  - simpl. rewrite (IHp b f), (IHq b f). tauto.
  - simpl. rewrite (IHp b f), (IHq b f). tauto.
  - simpl. split; intros Hall a.
    + specialize (Hall (quotient_mk (first_order_eq_quotient H) a)).
      change (semiformula_eval (first_order_eq_quotient_structure H)
        (fin_env_cons (quotient_mk (first_order_eq_quotient H) a)
          (fun i => quotient_mk (first_order_eq_quotient H) (b i)))
        (fun x => quotient_mk (first_order_eq_quotient H) (f x)) p)
        in Hall.
      rewrite <- first_order_eq_quotient_fin_env_cons in Hall.
      exact (proj1 (IHp (fin_env_cons a b) f) Hall).
    + pose (r := quotient_repr (first_order_eq_quotient H) a).
      specialize (Hall r).
      apply (proj2 (IHp (fin_env_cons r b) f)) in Hall.
      rewrite first_order_eq_quotient_fin_env_cons in Hall.
      unfold r in Hall.
      rewrite (quotient_mk_repr (first_order_eq_quotient H)) in Hall.
      exact Hall.
  - simpl. split; intros Hex.
    + destruct Hex as [a Ha].
      pose (r := quotient_repr (first_order_eq_quotient H) a).
      exists r. apply (proj1 (IHp (fin_env_cons r b) f)).
      change (semiformula_eval (first_order_eq_quotient_structure H)
        (fin_env_cons a
          (fun i => quotient_mk (first_order_eq_quotient H) (b i)))
        (fun x => quotient_mk (first_order_eq_quotient H) (f x)) p)
        in Ha.
      rewrite first_order_eq_quotient_fin_env_cons.
      unfold r.
      rewrite (quotient_mk_repr (first_order_eq_quotient H)).
      exact Ha.
    + destruct Hex as [a Ha].
      exists (quotient_mk (first_order_eq_quotient H) a).
      change (semiformula_eval (first_order_eq_quotient_structure H)
        (fin_env_cons (quotient_mk (first_order_eq_quotient H) a)
          (fun i => quotient_mk (first_order_eq_quotient H) (b i)))
        (fun x => quotient_mk (first_order_eq_quotient H) (f x)) p).
      rewrite <- first_order_eq_quotient_fin_env_cons.
      exact (proj2 (IHp (fin_env_cons a b) f) Ha).
Qed.

Lemma first_order_eq_quotient_eq_iff : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq)
    (a b : first_order_eq_quotient_carrier H),
  a = b <->
  first_order_eqv Str Heq
    (quotient_repr (first_order_eq_quotient H) a)
    (quotient_repr (first_order_eq_quotient H) b).
Proof.
  intros L M Str Heq H a b. split.
  - intro Hab. subst b. apply (first_order_eqv_refl H).
  - intro Hab.
    rewrite <- (quotient_mk_repr (first_order_eq_quotient H) a).
    rewrite <- (quotient_mk_repr (first_order_eq_quotient H) b).
    apply (proj2 (equivalence_class_mk_eq_iff
      (first_order_eqv_equivalence H) _ _)).
    exact Hab.
Qed.

Theorem first_order_eq_quotient_interprets_eq : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq),
  structure_interprets_eq (first_order_eq_quotient_structure H) Heq.
Proof.
  intros L M Str Heq H. constructor. intros a b.
  pose (Q := first_order_eq_quotient H).
  pose (ra := quotient_repr Q a).
  pose (rb := quotient_repr Q b).
  assert (Henv :
    fin_two a b =
    (fun i => quotient_mk Q (fin_two ra rb i))).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      fin_two a b j = quotient_mk Q (fin_two ra rb j)) _ _).
    - simpl. unfold ra, Q. symmetry.
      apply equivalence_class_mk_repr.
    - intro j. refine (@Fin.caseS' 0 j (fun u =>
        fin_two a b (Fin.FS u) =
        quotient_mk Q (fin_two ra rb (Fin.FS u))) _ _).
      + simpl. unfold rb, Q. symmetry.
        apply equivalence_class_mk_repr.
      + intros u; inversion u. }
  unfold semiformula_operator_eval.
  rewrite Henv.
  transitivity
    (semiformula_eval (first_order_eq_quotient_structure H)
      (fun i => quotient_mk Q (fin_two ra rb i))
      (fun x => quotient_mk Q
        ((fun y : Empty_set => match y with end) x))
      (semiformula_operator_sentence (semiformula_eq_operator Heq))).
  - apply semiformula_eval_free_ext. intros x _. destruct x.
  - transitivity
      (semiformula_eval Str (fin_two ra rb)
        (fun x : Empty_set => match x with end)
        (semiformula_operator_sentence (semiformula_eq_operator Heq))).
    + apply first_order_eq_quotient_formula_eval.
    + change (first_order_eqv Str Heq ra rb <-> a = b).
      symmetry. apply first_order_eq_quotient_eq_iff.
Qed.

Definition first_order_eq_quotient_model {L}
    (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms
      (first_order_model_structure m) Heq) :
  first_order_model L :=
  first_order_model_of_structure
    (inhabits (quotient_mk (first_order_eq_quotient H)
      (epsilon (first_order_model_nonempty m) (fun _ => True))))
    (first_order_eq_quotient_structure H).

Lemma first_order_eq_empty_bound_env_quotient : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq),
  @first_order_eq_empty_bound_env
      (first_order_eq_quotient_carrier H) =
  (fun i => quotient_mk (first_order_eq_quotient H)
    (@first_order_eq_empty_bound_env M i)).
Proof.
  intros. apply functional_extensionality. intro i.
  exact (Fin.case0 (fun i =>
    @first_order_eq_empty_bound_env
      (first_order_eq_quotient_carrier H) i =
    quotient_mk (first_order_eq_quotient H)
      (@first_order_eq_empty_bound_env M i)) i).
Qed.

Lemma first_order_eq_empty_free_env_quotient : forall L M
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms Str Heq),
  @first_order_eq_empty_free_env
      (first_order_eq_quotient_carrier H) =
  (fun x => quotient_mk (first_order_eq_quotient H)
    (@first_order_eq_empty_free_env M x)).
Proof.
  intros. apply functional_extensionality. intros [].
Qed.

Theorem first_order_eq_quotient_model_interprets_eq : forall L
    (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms
      (first_order_model_structure m) Heq),
  structure_interprets_eq
    (first_order_model_structure (first_order_eq_quotient_model H)) Heq.
Proof.
  intros. apply first_order_eq_quotient_interprets_eq.
Qed.

Theorem first_order_eq_quotient_elementary_equiv : forall L
    (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms
      (first_order_model_structure m) Heq),
  first_order_elementary_equiv m (first_order_eq_quotient_model H).
Proof.
  intros L m Heq H. constructor. intro p.
  unfold first_order_model_realize, sentence_realize, formula_eval.
  simpl. symmetry.
  change
    (semiformula_eval (first_order_eq_quotient_structure H)
       first_order_eq_empty_bound_env
       first_order_eq_empty_free_env p <->
     semiformula_eval (first_order_model_structure m)
       first_order_eq_empty_bound_env
       first_order_eq_empty_free_env p).
  rewrite first_order_eq_empty_bound_env_quotient.
  rewrite first_order_eq_empty_free_env_quotient.
  apply first_order_eq_quotient_formula_eval.
Qed.

Corollary first_order_eq_quotient_models_theory : forall L
    (m : first_order_model L)
    (Heq : semiformula_has_eq_operator L)
    (H : first_order_models_equality_axioms
      (first_order_model_structure m) Heq)
    (T : theory L),
  first_order_models_theory m T <->
  first_order_models_theory (first_order_eq_quotient_model H) T.
Proof.
  intros. apply first_order_elementary_equiv_models_theory.
  apply first_order_eq_quotient_elementary_equiv.
Qed.

(** * Restricting semantics to literal-equality models *)

Definition first_order_theory_proves_equality {L}
    (T : theory L) (Heq : semiformula_has_eq_operator L) : Prop :=
  forall sigma, @first_order_equality_axiom L Heq sigma ->
    first_order_theory_provable T sigma.

Definition first_order_theory_models_equality {L}
    (T : theory L) (Heq : semiformula_has_eq_operator L) : Prop :=
  forall m, first_order_models_theory m T ->
    first_order_models_equality_axioms
      (first_order_model_structure m) Heq.

Lemma first_order_theory_models_equality_of_proves : forall L
    (T : theory L) (Heq : semiformula_has_eq_operator L),
  first_order_theory_proves_equality T Heq ->
  first_order_theory_models_equality T Heq.
Proof.
  intros L T Heq Hproves m Hm.
  apply (proj1 (first_order_model_models_equality_theory_iff m Heq)).
  apply (proj2 (first_order_models_theory_iff m _)).
  intros sigma Hsigma.
  exact (@first_order_theory_proof_sound
    L T sigma (Hproves sigma Hsigma) m Hm).
Qed.

Theorem first_order_consequence_on_eq_models_iff : forall L
    (T : theory L) (sigma : sentence L)
    (Heq : semiformula_has_eq_operator L),
  first_order_theory_models_equality T Heq ->
  (first_order_consequence T sigma <->
   forall m,
     structure_interprets_eq (first_order_model_structure m) Heq ->
     first_order_models_theory m T ->
     first_order_model_realize m sigma).
Proof.
  intros L T sigma Heq Hequality. split.
  - intros Hconsequence m _ Hm. exact (Hconsequence m Hm).
  - intros Hrestricted m Hm.
    pose (Haxioms := Hequality m Hm).
    pose (q := first_order_eq_quotient_model Haxioms).
    assert (Hqstandard :
      structure_interprets_eq (first_order_model_structure q) Heq).
    { unfold q. apply first_order_eq_quotient_model_interprets_eq. }
    assert (Hqmodels : first_order_models_theory q T).
    { unfold q. apply (proj1
        (first_order_eq_quotient_models_theory Haxioms T)).
      exact Hm. }
    pose proof (Hrestricted q Hqstandard Hqmodels) as Hq.
    apply (proj2 (first_order_elementary_equiv_realize
      (first_order_eq_quotient_elementary_equiv Haxioms) sigma)).
    exact Hq.
Qed.

Corollary first_order_consequence_on_eq_models_of_proves_iff : forall L
    (T : theory L) (sigma : sentence L)
    (Heq : semiformula_has_eq_operator L),
  first_order_theory_proves_equality T Heq ->
  (first_order_consequence T sigma <->
   forall m,
     structure_interprets_eq (first_order_model_structure m) Heq ->
     first_order_models_theory m T ->
     first_order_model_realize m sigma).
Proof.
  intros. apply first_order_consequence_on_eq_models_iff.
  now apply first_order_theory_models_equality_of_proves.
Qed.

Theorem first_order_satisfiable_on_eq_models_iff : forall L
    (T : theory L) (Heq : semiformula_has_eq_operator L),
  first_order_theory_models_equality T Heq ->
  (first_order_satisfiable T <->
   exists m,
     structure_interprets_eq (first_order_model_structure m) Heq /\
     first_order_models_theory m T).
Proof.
  intros L T Heq Hequality. split.
  - intros [m Hm].
    pose (Haxioms := Hequality m Hm).
    exists (first_order_eq_quotient_model Haxioms). split.
    + apply first_order_eq_quotient_model_interprets_eq.
    + apply (proj1 (first_order_eq_quotient_models_theory Haxioms T)).
      exact Hm.
  - intros [m [_ Hm]]. now exists m.
Qed.

Corollary first_order_satisfiable_on_eq_models_of_proves_iff : forall L
    (T : theory L) (Heq : semiformula_has_eq_operator L),
  first_order_theory_proves_equality T Heq ->
  (first_order_satisfiable T <->
   exists m,
     structure_interprets_eq (first_order_model_structure m) Heq /\
     first_order_models_theory m T).
Proof.
  intros. apply first_order_satisfiable_on_eq_models_iff.
  now apply first_order_theory_models_equality_of_proves.
Qed.

(** * Unique existence *)

Definition first_order_exists_unique_reindex {n} :
    Fin.t (S n) -> Fin.t (S (S n)) :=
  fun i => @Fin.caseS' n i (fun _ => Fin.t (S (S n)))
    Fin.F1 (fun j => Fin.FS (Fin.FS j)).

Definition first_order_exists_unique {L X n}
    (Heq : semiformula_has_eq_operator L)
    (p : semiformula L X (S n)) : semiformula L X n :=
  Semiformula_exists
    (Semiformula_and p
      (Semiformula_all
        (semiformula_imp
          (semiformula_rewrite
            (rew_map first_order_exists_unique_reindex (fun x => x)) p)
          (first_order_eq_atom Heq
            (@Semiterm_bvar L X (S (S n)) Fin.F1)
            (@Semiterm_bvar L X (S (S n)) (Fin.FS Fin.F1)))))).

Lemma first_order_exists_unique_reindex_env : forall M n
    (z a : M) (b : Fin.t n -> M),
  (fun i => fin_env_cons z (fin_env_cons a b)
      (first_order_exists_unique_reindex i)) =
  fin_env_cons z b.
Proof.
  intros M n z a b. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    fin_env_cons z (fin_env_cons a b)
      (first_order_exists_unique_reindex j) =
    fin_env_cons z b j) eq_refl _).
  intro j. reflexivity.
Qed.

Theorem first_order_exists_unique_eval : forall L M X n
    (Str : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (Hstandard : structure_interprets_eq Str Heq)
    (p : semiformula L X (S n))
    (b : Fin.t n -> M) (f : X -> M),
  semiformula_eval Str b f (first_order_exists_unique Heq p) <->
  exists a,
    semiformula_eval Str (fin_env_cons a b) f p /\
    forall z,
      semiformula_eval Str (fin_env_cons z b) f p -> z = a.
Proof.
  intros L M X n Str Heq Hstandard p b f.
  unfold first_order_exists_unique. simpl. split.
  - intros [a [Ha Hunique]]. exists a. split; [exact Ha |].
    intros z Hz. specialize (Hunique z).
    assert (Hz' :
      semiformula_eval Str (fin_env_cons z (fin_env_cons a b)) f
        (semiformula_rewrite
          (rew_map first_order_exists_unique_reindex (fun x => x)) p)).
    { apply (proj2 (semiformula_eval_map Str
        (fin_env_cons z (fin_env_cons a b)) f
        first_order_exists_unique_reindex (fun x => x) p)).
      rewrite first_order_exists_unique_reindex_env. exact Hz. }
    pose proof ((proj1 (semiformula_eval_imp Str
      (fin_env_cons z (fin_env_cons a b)) f _ _)) Hunique Hz')
      as Hequal.
    rewrite first_order_eq_atom_eval in Hequal.
    simpl in Hequal. unfold first_order_eqv in Hequal.
    exact (proj1 (structure_eq_operator Hstandard z a) Hequal).
  - intros [a [Ha Hunique]]. exists a. split; [exact Ha |].
    intro z. apply (proj2 (semiformula_eval_imp Str
      (fin_env_cons z (fin_env_cons a b)) f _ _)).
    intro Hz.
    rewrite first_order_eq_atom_eval. simpl.
    unfold first_order_eqv.
    apply (proj2 (structure_eq_operator Hstandard z a)).
    apply Hunique.
    apply (proj1 (semiformula_eval_map Str
      (fin_env_cons z (fin_env_cons a b)) f
      first_order_exists_unique_reindex (fun x => x) p)) in Hz.
    rewrite first_order_exists_unique_reindex_env in Hz.
    exact Hz.
Qed.
