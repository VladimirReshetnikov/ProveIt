(**
  Semantic direct interpretations.

  This file ports the reusable model-theoretic core of
  [Foundation/FirstOrder/Interpretation.lean].  A direct translation assigns
  source formulas to the target domain, relations, and function graphs.  A
  realization packages the source-side existence, uniqueness, and equality
  obligations; the induced target structure is then obtained by unique
  choice on the domain subtype.  The construction is deliberately
  representation-independent: syntax-level translation and proof-calculus
  adapters can be layered on top of this semantic API.
*)

From Stdlib Require Import Logic.ClassicalEpsilon Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
From Foundation.Vorspiel Require Import ExistsUnique.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics ModelTheory OperatorSemantics Elementary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A direct translation presents the source formulas used to describe the
    target domain, relation symbols, and function graphs.  A function graph
    has one output variable at the head followed by its input variables. *)
Record direct_translation (L1 L2 : language) : Type := {
  direct_translation_domain : semisentence L1 1;
  direct_translation_rel : forall k, language_rel L2 k -> semisentence L1 k;
  direct_translation_func : forall k, language_func L2 k -> semisentence L1 (S k)
}.

Arguments direct_translation_domain {L1 L2} _.
Arguments direct_translation_rel {L1 L2} _ _ _.
Arguments direct_translation_func {L1 L2} _ _ _.

Definition direct_translation_empty_env {M : Type} : Empty_set -> M :=
  fun x => match x with end.

Definition direct_translation_dom {L1 L2 M}
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (x : M) : Prop :=
  semiformula_eval S (fin_one x) (direct_translation_empty_env (M := M))
    (direct_translation_domain tr).

Definition direct_translation_graph {L1 L2 M}
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    {k} (f : language_func L2 k) (y : M) (v : Fin.t k -> M) : Prop :=
  semiformula_eval S (fin_env_cons y v)
    (direct_translation_empty_env (M := M))
    (direct_translation_func tr k f).

Lemma direct_translation_dom_iff : forall L1 L2 M
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (x : M),
  direct_translation_dom tr S x <->
  semiformula_eval S (fin_one x) (direct_translation_empty_env (M := M))
    (direct_translation_domain tr).
Proof. intros; split; trivial. Qed.

Lemma direct_translation_graph_iff : forall L1 L2 M
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) k
    (f : language_func L2 k) (y : M) (v : Fin.t k -> M),
  direct_translation_graph tr S f y v <->
  semiformula_eval S (fin_env_cons y v)
    (direct_translation_empty_env (M := M))
    (direct_translation_func tr k f).
Proof. intros; split; trivial. Qed.

(** The semantic obligations needed to build the interpreted structure.  The
    equality relation is selected from the target language itself, so the
    resulting model can expose the standard [structure_interprets_eq]
    capability without any source-language typeclass assumptions. *)
Record direct_translation_realization
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    (Heq : language_has_eq L2) : Prop := {
  direct_translation_domain_nonempty :
    exists x : M, direct_translation_dom tr S x;
  direct_translation_func_defined :
    forall k (f : language_func L2 k) (v : Fin.t k -> M),
      (forall i, direct_translation_dom tr S (v i)) ->
      exists! y : M,
        direct_translation_dom tr S y /\
        direct_translation_graph tr S f y v;
  direct_translation_preserve_eq :
    forall x y : M,
      direct_translation_dom tr S x ->
      direct_translation_dom tr S y ->
      (semiformula_eval S (fin_two x y)
        (direct_translation_empty_env (M := M))
        (direct_translation_rel tr 2 (language_eq Heq)) <-> x = y)
}.

Arguments direct_translation_domain_nonempty
  {L1 L2 M tr S Heq} _.
Arguments direct_translation_func_defined
  {L1 L2 M tr S Heq} _ _ _ _ _.
Arguments direct_translation_preserve_eq
  {L1 L2 M tr S Heq} _ _ _ _ _.

Definition direct_translation_model_carrier
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) : Type :=
  {x : M | direct_translation_dom tr S x}.

Definition direct_translation_model_func_relation
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    {k} (f : language_func L2 k) (v : Fin.t k -> M) : M -> Prop :=
  fun y => direct_translation_dom tr S y /\
    direct_translation_graph tr S f y v.

Definition direct_translation_model_func_val
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    {k} (f : language_func L2 k)
    (v : Fin.t k -> @direct_translation_model_carrier L1 L2 M tr S)
    : @direct_translation_model_carrier L1 L2 M tr S :=
  exist _
    (choose_unique
      (@direct_translation_model_func_relation L1 L2 M tr S k f
        (fun i => proj1_sig (v i)))
      (direct_translation_func_defined Hreal k f
        (fun i => proj1_sig (v i))
        (fun i => proj2_sig (v i))))
    (proj1
      (choose_unique_spec
        (direct_translation_func_defined Hreal k f
          (fun i => proj1_sig (v i))
          (fun i => proj2_sig (v i))))).

Lemma direct_translation_model_func_val_spec :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    k (f : language_func L2 k)
    (v : Fin.t k -> @direct_translation_model_carrier L1 L2 M tr S),
  direct_translation_dom tr S
      (proj1_sig (@direct_translation_model_func_val
        L1 L2 M tr S Heq Hreal k f v)) /\
  direct_translation_graph tr S f
      (proj1_sig (@direct_translation_model_func_val
        L1 L2 M tr S Heq Hreal k f v))
      (fun i => proj1_sig (v i)).
Proof.
  intros L1 L2 M tr S Heq Hreal k f v.
  unfold direct_translation_model_func_val,
    direct_translation_model_func_relation.
  exact (@choose_unique_spec M
    (fun y => direct_translation_dom tr S y /\
      direct_translation_graph tr S f y
        (fun i => proj1_sig (v i)))
    (direct_translation_func_defined Hreal k f
      (fun i => proj1_sig (v i))
      (fun i => proj2_sig (v i)))).
Qed.

Definition direct_translation_model_structure
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq) :
    first_order_structure L2
      (@direct_translation_model_carrier L1 L2 M tr S) :=
  @Build_first_order_structure L2
    (@direct_translation_model_carrier L1 L2 M tr S)
    (fun k f v =>
      @direct_translation_model_func_val L1 L2 M tr S Heq Hreal k f v)
    (fun k r v =>
      semiformula_eval S
        (fun i => proj1_sig (v i))
        (direct_translation_empty_env (M := M))
        (direct_translation_rel tr k r)).

Lemma direct_translation_model_structure_rel :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    k (r : language_rel L2 k)
    (v : Fin.t k -> @direct_translation_model_carrier L1 L2 M tr S),
  structure_rel
      (@direct_translation_model_structure L1 L2 M tr S Heq Hreal) r v <->
  semiformula_eval S
    (fun i => proj1_sig (v i))
    (direct_translation_empty_env (M := M))
    (direct_translation_rel tr k r).
Proof. intros; split; trivial. Qed.

Lemma direct_translation_model_func_iff :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    k (f : language_func L2 k)
    (y : @direct_translation_model_carrier L1 L2 M tr S)
    (v : Fin.t k -> @direct_translation_model_carrier L1 L2 M tr S),
  y = structure_func
      (@direct_translation_model_structure L1 L2 M tr S Heq Hreal) f v <->
  direct_translation_graph tr S f (proj1_sig y)
    (fun i => proj1_sig (v i)).
Proof.
  intros L1 L2 M tr S Heq Hreal k f y v.
  split.
  - intro H; subst y.
    apply (proj2 (@direct_translation_model_func_val_spec
      L1 L2 M tr S Heq Hreal k f v)).
  - intro Hgraph.
    destruct y as [y Hy].
    unfold direct_translation_model_structure,
      direct_translation_model_func_val.
    simpl.
    assert (Hyz :
        y = choose_unique
          (fun z => direct_translation_dom tr S z /\
            direct_translation_graph tr S f z
              (fun i => proj1_sig (v i)))
          (direct_translation_func_defined Hreal k f
            (fun i => proj1_sig (v i))
            (fun i => proj2_sig (v i)))).
    { apply (@choose_unique_uniq M
        (fun z => direct_translation_dom tr S z /\
          direct_translation_graph tr S f z
            (fun i => proj1_sig (v i)))
        (direct_translation_func_defined Hreal k f
          (fun i => proj1_sig (v i))
          (fun i => proj2_sig (v i)))
        y).
      exact (conj Hy Hgraph). }
    subst y.
    cbn [direct_translation_model_func_val].
    unfold direct_translation_model_func_relation.
    refine (@eq_sig M (fun x => direct_translation_dom tr S x)
      (exist (fun x => direct_translation_dom tr S x)
        (choose_unique
          (fun z => direct_translation_dom tr S z /\
            direct_translation_graph tr S f z
              (fun i => proj1_sig (v i)))
          (direct_translation_func_defined Hreal k f
            (fun i => proj1_sig (v i))
            (fun i => proj2_sig (v i))))
        Hy)
      (@direct_translation_model_func_val
        L1 L2 M tr S Heq Hreal k f v) eq_refl _).
    apply proof_irrelevance.
Qed.

Lemma direct_translation_model_func_iff' :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    k (f : language_func L2 k)
    (y : M)
    (v : Fin.t k -> @direct_translation_model_carrier L1 L2 M tr S),
  y = proj1_sig (structure_func
      (@direct_translation_model_structure L1 L2 M tr S Heq Hreal) f v) <->
  direct_translation_dom tr S y /\
  direct_translation_graph tr S f y (fun i => proj1_sig (v i)).
Proof.
  intros L1 L2 M tr S Heq Hreal k f y v.
  split.
  - intro H; subst y.
    apply (@direct_translation_model_func_val_spec
      L1 L2 M tr S Heq Hreal k f v).
  - intros [Hy Hgraph].
    apply (@choose_unique_uniq M
      (fun z => direct_translation_dom tr S z /\
        direct_translation_graph tr S f z
          (fun i => proj1_sig (v i)))
      (direct_translation_func_defined Hreal k f
        (fun i => proj1_sig (v i))
        (fun i => proj2_sig (v i))) y).
    exact (conj Hy Hgraph).
Qed.

Lemma direct_translation_model_semiterm_val_domain :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    X n (b : Fin.t n -> @direct_translation_model_carrier L1 L2 M tr S)
    (f : X -> @direct_translation_model_carrier L1 L2 M tr S)
    (t : semiterm L2 X n),
  direct_translation_dom tr S
    (proj1_sig (semiterm_val
      (@direct_translation_model_structure L1 L2 M tr S Heq Hreal)
      b f t)).
Proof.
  intros L1 L2 M tr S Heq Hreal X n b f t.
  induction t as [i | x | k F v IH]; simpl.
  - apply proj2_sig.
  - apply proj2_sig.
  - apply (proj1 (@direct_translation_model_func_val_spec
      L1 L2 M tr S Heq Hreal k F
      (fun i => semiterm_val
        (@direct_translation_model_structure L1 L2 M tr S Heq Hreal)
        b f (v i)))).
Qed.

Lemma direct_translation_model_atomic_iff :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq)
    X n k (r : language_rel L2 k)
    (b : Fin.t n -> @direct_translation_model_carrier L1 L2 M tr S)
    (f : X -> @direct_translation_model_carrier L1 L2 M tr S)
    (v : Fin.t k -> semiterm L2 X n),
  structure_rel
      (@direct_translation_model_structure L1 L2 M tr S Heq Hreal) r
      (fun i => semiterm_val
        (@direct_translation_model_structure L1 L2 M tr S Heq Hreal)
        b f (v i)) <->
  semiformula_eval S
    (fun i => proj1_sig
      (semiterm_val
        (@direct_translation_model_structure L1 L2 M tr S Heq Hreal)
        b f (v i)))
    (direct_translation_empty_env (M := M))
    (direct_translation_rel tr k r).
Proof.
  intros. apply direct_translation_model_structure_rel.
Qed.

Lemma direct_translation_model_nonempty :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq),
  inhabited (@direct_translation_model_carrier L1 L2 M tr S).
Proof.
  intros L1 L2 M tr S Heq Hreal.
  destruct (direct_translation_domain_nonempty Hreal) as [x Hx].
  exact (inhabits (exist _ x Hx)).
Qed.

Definition direct_translation_model
    (L1 L2 : language) (M : Type)
    (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M)
    (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq) :
    first_order_model L2 :=
  first_order_model_of_structure
    (@direct_translation_model_nonempty L1 L2 M tr S Heq Hreal)
    (@direct_translation_model_structure L1 L2 M tr S Heq Hreal).

Lemma direct_translation_model_interprets_eq :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq),
  structure_interprets_eq
    (@direct_translation_model_structure L1 L2 M tr S Heq Hreal)
    (semiformula_eq_operator_of_language Heq).
Proof.
  intros L1 L2 M tr S Heq Hreal.
  constructor. intros a b.
  rewrite semiformula_eq_operator_eval_of_language.
  simpl.
  assert (Hvec :
    (fun i : Fin.t 2 => proj1_sig (fin_two a b i)) =
    fin_two (proj1_sig a) (proj1_sig b)).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      proj1_sig (fin_two a b j) =
      fin_two (proj1_sig a) (proj1_sig b) j) eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      proj1_sig (fin_two a b (Fin.FS q)) =
      fin_two (proj1_sig a) (proj1_sig b) (Fin.FS q)) eq_refl _).
    intros q; inversion q. }
  rewrite Hvec.
  rewrite (direct_translation_preserve_eq Hreal
    (proj1_sig a) (proj1_sig b) (proj2_sig a) (proj2_sig b)).
  split.
  - intro H. apply (@eq_sig M (fun x => direct_translation_dom tr S x)
      a b H). apply proof_irrelevance.
  - intro H; now inversion H.
Qed.

Lemma direct_translation_model_domain :
  forall L1 L2 M (tr : direct_translation L1 L2)
    (S : first_order_structure L1 M) (Heq : language_has_eq L2)
    (Hreal : @direct_translation_realization L1 L2 M tr S Heq),
  first_order_model_domain
    (@direct_translation_model L1 L2 M tr S Heq Hreal) =
  @direct_translation_model_carrier L1 L2 M tr S.
Proof. reflexivity. Qed.
