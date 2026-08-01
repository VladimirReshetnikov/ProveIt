(**
  Semantic equality axioms and congruence.

  This ports the central semantic layer of
  [Foundation/FirstOrder/Basic/Eq.lean].  Rather than tying the results to a
  particular syntactic presentation of the equality-axiom theory, the model
  laws are an explicit capability record.  This both generalizes the source
  lemmas and isolates the exact hypotheses needed by later quotient work.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.FunctionalExtensionality.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Logic.PropExtensionality.
From Foundation.Vorspiel Require Import Quotient.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics ModelTheory Elementary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

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

Definition first_order_eq_empty_bound_env {A} : Fin.t 0 -> A :=
  fun i => match i with end.

Definition first_order_eq_empty_free_env {A} : Empty_set -> A :=
  fun x => match x with end.

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
