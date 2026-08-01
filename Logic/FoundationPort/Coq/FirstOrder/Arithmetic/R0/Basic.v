(**
  Semantic core of Cobham's arithmetic theory R0.

  The source presents four first-order axiom schemes and then repeatedly uses
  only their consequences in a model.  Packaging those consequences directly
  keeps downstream reductions independent of a particular proof calculus while
  retaining the exact numeral arithmetic and finite-interval content.
*)

From Stdlib Require Import Arith.PeanoNat Lia Logic.Classical_Prop Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Quantifier Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Eq Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  ModelTheory RewriteClosure Semantics OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The concrete Cobham-R0 theory *)

Definition r0_numeral_add_sentence (n m : nat) : sentence oring_language :=
  arithmetic_eq_formula
    (arithmetic_add_term (arithmetic_numeral_term n)
      (arithmetic_numeral_term m))
    (arithmetic_numeral_term (n + m)).

Definition r0_numeral_mul_sentence (n m : nat) : sentence oring_language :=
  arithmetic_eq_formula
    (arithmetic_mul_term (arithmetic_numeral_term n)
      (arithmetic_numeral_term m))
    (arithmetic_numeral_term (n * m)).

Definition r0_numeral_ne_sentence (n m : nat) : sentence oring_language :=
  semiformula_neg
    (arithmetic_eq_formula (arithmetic_numeral_term n)
      (arithmetic_numeral_term m)).

Definition r0_initial_segment_sentence (n : nat) : sentence oring_language :=
  first_all_closure
    (semiformula_universal_quantifier oring_language Empty_set) 1
    (semiformula_iff
      (arithmetic_lt_formula
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1)
        (arithmetic_numeral_term n))
      (arithmetic_eq_disjunction n
        (@Semiterm_bvar oring_language Empty_set 1 Fin.F1))).

Inductive r0_axiom : theory oring_language :=
| R0Equality : forall sigma,
    first_order_equality_axiom oring_language_eq_operator sigma ->
    r0_axiom sigma
| R0NumeralAdd : forall n m,
    r0_axiom (r0_numeral_add_sentence n m)
| R0NumeralMul : forall n m,
    r0_axiom (r0_numeral_mul_sentence n m)
| R0NumeralNe : forall n m,
    n <> m -> r0_axiom (r0_numeral_ne_sentence n m)
| R0InitialSegment : forall n,
    r0_axiom (r0_initial_segment_sentence n).

Theorem r0_proves_equality :
  first_order_theory_proves_equality r0_axiom oring_language_eq_operator.
Proof.
  intros sigma Hsigma.
  exact (@generic_axiomatized_by_axiom
    (theory oring_language) (sentence oring_language)
    (first_order_theory_entailment oring_language)
    (generic_predicate_adjunctive_set (sentence oring_language))
    (first_order_theory_axiomatized oring_language)
    r0_axiom sigma (R0Equality Hsigma)).
Qed.

Definition r0_empty_bound_env : Fin.t 0 -> nat :=
  fun i => match i with end.

Definition r0_empty_free_env {A} : Empty_set -> A :=
  fun x => match x with end.

Lemma r0_numeral_add_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M) n m,
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str (r0_numeral_add_sentence n m) <->
   oring_add O (oring_numeral O n) (oring_numeral O m) =
   oring_numeral O (n + m)).
Proof.
  intros M Str O n m Horing. unfold sentence_realize,
    r0_numeral_add_sentence, formula_eval.
  rewrite (@arithmetic_eq_formula_eval M Empty_set 0 Str _ _ O _ _ Horing).
  rewrite (@arithmetic_add_term_val M Empty_set 0 Str _ _ O _ _ Horing).
  repeat rewrite (@arithmetic_numeral_term_val M Empty_set 0 Str _ _ O _ Horing).
  reflexivity.
Qed.

Lemma r0_numeral_mul_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M) n m,
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str (r0_numeral_mul_sentence n m) <->
   oring_mul O (oring_numeral O n) (oring_numeral O m) =
   oring_numeral O (n * m)).
Proof.
  intros M Str O n m Horing. unfold sentence_realize,
    r0_numeral_mul_sentence, formula_eval.
  rewrite (@arithmetic_eq_formula_eval M Empty_set 0 Str _ _ O _ _ Horing).
  rewrite (@arithmetic_mul_term_val M Empty_set 0 Str _ _ O _ _ Horing).
  repeat rewrite (@arithmetic_numeral_term_val M Empty_set 0 Str _ _ O _ Horing).
  reflexivity.
Qed.

Lemma r0_numeral_ne_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M) n m,
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str (r0_numeral_ne_sentence n m) <->
   oring_numeral O n <> oring_numeral O m).
Proof.
  intros M Str O n m Horing. unfold sentence_realize,
    r0_numeral_ne_sentence, formula_eval.
  rewrite semiformula_eval_neg.
  rewrite (@arithmetic_eq_formula_eval M Empty_set 0 Str _ _ O _ _ Horing).
  repeat rewrite (@arithmetic_numeral_term_val M Empty_set 0 Str _ _ O _ Horing).
  reflexivity.
Qed.

Lemma r0_initial_segment_realize_iff : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M) n,
  structure_interprets_oring Str oring_language_structure O ->
  (sentence_realize Str (r0_initial_segment_sentence n) <->
   forall x,
     oring_lt O x (oring_numeral O n) <->
     exists i : Fin.t n,
       x = oring_numeral O (proj1_sig (Fin.to_nat i))).
Proof.
  intros M Str O n Horing. unfold sentence_realize,
    r0_initial_segment_sentence, formula_eval.
  rewrite semiformula_eval_all_closure. split.
  - intros H x. specialize (H (fin_one x)).
    rewrite semiformula_eval_iff in H.
    rewrite (@arithmetic_lt_formula_eval M Empty_set 1 Str (fin_one x)
      r0_empty_free_env O _ _ Horing) in H.
    rewrite (@arithmetic_numeral_term_val M Empty_set 1 Str (fin_one x)
      r0_empty_free_env O _ Horing) in H.
    rewrite (@arithmetic_eq_disjunction_eval M Empty_set 1 Str (fin_one x)
      r0_empty_free_env O n _ Horing) in H.
    simpl in H. exact H.
  - intros H e. specialize (H (e Fin.F1)).
    rewrite semiformula_eval_iff.
    rewrite (@arithmetic_lt_formula_eval M Empty_set 1 Str e
      r0_empty_free_env O _ _ Horing).
    rewrite (@arithmetic_numeral_term_val M Empty_set 1 Str e
      r0_empty_free_env O _ Horing).
    rewrite (@arithmetic_eq_disjunction_eval M Empty_set 1 Str e
      r0_empty_free_env O n _ Horing).
    simpl. exact H.
Qed.

Record r0_laws {M : Type} (O : oring_carrier M) : Prop := {
  r0_numeral_add : forall n m,
    oring_add O (oring_numeral O n) (oring_numeral O m) =
    oring_numeral O (n + m);
  r0_numeral_mul : forall n m,
    oring_mul O (oring_numeral O n) (oring_numeral O m) =
    oring_numeral O (n * m);
  r0_numeral_ne : forall n m,
    n <> m -> oring_numeral O n <> oring_numeral O m;
  r0_lt_numeral : forall n x,
    oring_lt O x (oring_numeral O n) <->
    exists i, i < n /\ x = oring_numeral O i
}.

Lemma r0_numeral_eq_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n m,
  oring_numeral O n = oring_numeral O m <-> n = m.
Proof.
  intros M O H n m. split.
  - intro Heq. destruct (Nat.eq_dec n m); [assumption|].
    exfalso. exact (@r0_numeral_ne M O H n m n0 Heq).
  - now intros ->.
Qed.

Lemma r0_numeral_lt_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n m,
  oring_lt O (oring_numeral O n) (oring_numeral O m) <-> n < m.
Proof.
  intros M O H n m. split.
  - intro Hlt.
    destruct (proj1 (@r0_lt_numeral M O H m (oring_numeral O n)) Hlt)
      as [i [Him Hni]].
    apply (proj1 (r0_numeral_eq_iff H n i)) in Hni.
    now subst i.
  - intro Hnm. apply (proj2 (@r0_lt_numeral M O H m
      (oring_numeral O n))).
    exists n. now split.
Qed.

Lemma r0_lt_numeral_fin_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) <->
  exists i : Fin.t n,
    x = oring_numeral O (proj1_sig (Fin.to_nat i)).
Proof.
  intros M O H n x. rewrite (@r0_lt_numeral M O H n x).
  split.
  - intros [i [Hin Hx]]. exists (Fin.of_nat_lt Hin).
    rewrite Fin.to_nat_of_nat. exact Hx.
  - intros [i Hx]. exists (proj1_sig (Fin.to_nat i)). split.
    + exact (proj2_sig (Fin.to_nat i)).
    + exact Hx.
Qed.

Theorem first_order_model_models_r0_iff : forall
    (m : first_order_model oring_language)
    (O : oring_carrier (first_order_model_domain m)),
  structure_interprets_oring (first_order_model_structure m)
    oring_language_structure O ->
  (first_order_models_theory m r0_axiom <-> r0_laws O).
Proof.
  intros m O Horing. split.
  - intro Hmodels. constructor.
    + intros n q. apply (proj1 (@r0_numeral_add_realize_iff _
        (first_order_model_structure m) O n q Horing)).
      exact (first_order_models_of_member Hmodels (R0NumeralAdd n q)).
    + intros n q. apply (proj1 (@r0_numeral_mul_realize_iff _
        (first_order_model_structure m) O n q Horing)).
      exact (first_order_models_of_member Hmodels (R0NumeralMul n q)).
    + intros n q Hne. apply (proj1 (@r0_numeral_ne_realize_iff _
        (first_order_model_structure m) O n q Horing)).
      exact (first_order_models_of_member Hmodels (R0NumeralNe Hne)).
    + intros n x.
      pose proof (proj1 (@r0_initial_segment_realize_iff _
        (first_order_model_structure m) O n Horing)
        (first_order_models_of_member Hmodels (R0InitialSegment n))) as Hfin.
      specialize (Hfin x). split.
      * intro Hx. destruct (proj1 Hfin Hx) as [i Hi].
        exists (proj1_sig (Fin.to_nat i)). split.
        -- exact (proj2_sig (Fin.to_nat i)).
        -- exact Hi.
      * intros [i [Hin Hi]]. apply (proj2 Hfin).
        exists (Fin.of_nat_lt Hin). rewrite Fin.to_nat_of_nat. exact Hi.
  - intro Hlaws. apply (proj2 (first_order_models_theory_iff m _)).
    intros sigma Hsigma. destruct Hsigma.
    + exact (first_order_models_of_member
        (first_order_model_models_equality_theory_of_interprets_eq
          (structure_oring_eq Horing)) H).
    + apply (proj2 (@r0_numeral_add_realize_iff _
        (first_order_model_structure m) O n m0 Horing)).
      exact (r0_numeral_add Hlaws n m0).
    + apply (proj2 (@r0_numeral_mul_realize_iff _
        (first_order_model_structure m) O n m0 Horing)).
      exact (r0_numeral_mul Hlaws n m0).
    + apply (proj2 (@r0_numeral_ne_realize_iff _
        (first_order_model_structure m) O n m0 Horing)).
      exact (r0_numeral_ne Hlaws H).
    + apply (proj2 (@r0_initial_segment_realize_iff _
        (first_order_model_structure m) O n Horing)).
      intros x. exact (r0_lt_numeral_fin_iff Hlaws n x).
Qed.

Definition nat_r0_laws : r0_laws nat_oring_carrier.
Proof.
  constructor.
  - intros n m. rewrite !nat_oring_numeral. reflexivity.
  - intros n m. rewrite !nat_oring_numeral. reflexivity.
  - intros n m Hne. rewrite !nat_oring_numeral. exact Hne.
  - intros n x. rewrite !nat_oring_numeral.
    cbn [nat_oring_carrier]. split.
    + intro Hx. exists x. split.
      * exact Hx.
      * symmetry. apply nat_oring_numeral.
    + intros [i [Hin ->]]. rewrite nat_oring_numeral.
      change (i < n). exact Hin.
Defined.

Theorem nat_standard_model_models_r0 :
  first_order_models_theory nat_standard_model r0_axiom.
Proof.
  apply (proj2 (@first_order_model_models_r0_iff
    nat_standard_model nat_oring_carrier nat_standard_structure_interprets)).
  exact nat_r0_laws.
Qed.

Theorem r0_consistent :
  generic_consistent (first_order_theory_entailment oring_language) r0_axiom.
Proof.
  exact (first_order_theory_consistent_of_model nat_standard_model_models_r0).
Qed.

Theorem r0_proof_complete : forall sigma : sentence oring_language,
  (forall (m : first_order_model oring_language)
          (O : oring_carrier (first_order_model_domain m)),
    structure_interprets_oring (first_order_model_structure m)
      oring_language_structure O ->
    r0_laws O ->
    first_order_model_realize m sigma) ->
  first_order_theory_provable r0_axiom sigma.
Proof.
  intros sigma Hvalid.
  apply (arithmetic_theory_proof_complete r0_proves_equality).
  intros m O Horing Hmodels.
  apply (Hvalid m O Horing).
  now apply (proj1 (@first_order_model_models_r0_iff m O Horing)).
Qed.

(** The source's omega-plus-one R0 countermodel.  Unlike the Q countermodel
    used elsewhere, every operation involving the extra top point collapses
    to zero; hence [top + 0 <> top]. *)
Definition r0_omega_add_one : Type := option nat.

Definition r0_omega_add_one_add
    (x y : r0_omega_add_one) : r0_omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n + m)
  | _, _ => Some 0
  end.

Definition r0_omega_add_one_mul
    (x y : r0_omega_add_one) : r0_omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n * m)
  | _, _ => Some 0
  end.

Definition r0_omega_add_one_lt
    (x y : r0_omega_add_one) : Prop :=
  match x, y with
  | Some n, Some m => n < m
  | Some _, None => True
  | None, _ => False
  end.

Definition r0_omega_add_one_oring : oring_carrier r0_omega_add_one :=
  {| oring_zero := Some 0;
     oring_one := Some 1;
     oring_add := r0_omega_add_one_add;
     oring_mul := r0_omega_add_one_mul;
     oring_lt := r0_omega_add_one_lt |}.

Lemma r0_omega_add_one_numeral : forall n,
  oring_numeral r0_omega_add_one_oring n = Some n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct n as [|n]; [reflexivity|].
  change (r0_omega_add_one_add
    (oring_numeral r0_omega_add_one_oring (S n)) (Some 1) =
    Some (S (S n))).
  rewrite IH. cbn [r0_omega_add_one_add]. f_equal. lia.
Qed.

Definition r0_omega_add_one_laws : r0_laws r0_omega_add_one_oring.
Proof.
  constructor.
  - intros n m. rewrite !r0_omega_add_one_numeral.
    cbv [r0_omega_add_one_oring r0_omega_add_one_add oring_add]. f_equal.
  - intros n m. rewrite !r0_omega_add_one_numeral.
    cbv [r0_omega_add_one_oring r0_omega_add_one_mul oring_mul]. f_equal.
  - intros n m Hne. rewrite !r0_omega_add_one_numeral.
    intro Heq. injection Heq. contradiction.
  - intros n [x|].
    + rewrite r0_omega_add_one_numeral.
      cbv [r0_omega_add_one_oring r0_omega_add_one_lt oring_lt]. split.
      * intro Hx. exists x. split; [exact Hx|].
        symmetry. apply r0_omega_add_one_numeral.
      * intros [i [Hin Hi]]. rewrite r0_omega_add_one_numeral in Hi.
        injection Hi. intro Hxi. subst i. exact Hin.
    + rewrite r0_omega_add_one_numeral.
      cbv [r0_omega_add_one_oring r0_omega_add_one_lt oring_lt]. split.
      * contradiction.
      * intros [i [Hin Hi]]. rewrite r0_omega_add_one_numeral in Hi.
        discriminate.
Defined.

Definition r0_omega_add_one_model : first_order_model oring_language :=
  first_order_model_of_structure (inhabits None)
    (oring_standard_structure r0_omega_add_one_oring).

Theorem r0_omega_add_one_model_models_r0 :
  first_order_models_theory r0_omega_add_one_model r0_axiom.
Proof.
  apply (proj2 (@first_order_model_models_r0_iff
    r0_omega_add_one_model r0_omega_add_one_oring
    (oring_standard_structure_interprets r0_omega_add_one_oring))).
  exact r0_omega_add_one_laws.
Qed.

Lemma r0_omega_add_one_top_add_zero :
  r0_omega_add_one_add None (oring_zero r0_omega_add_one_oring) = Some 0.
Proof. reflexivity. Qed.
