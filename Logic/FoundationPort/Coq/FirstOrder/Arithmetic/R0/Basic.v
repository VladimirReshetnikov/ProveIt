(**
  Semantic core of Cobham's arithmetic theory R0.

  The source presents four first-order axiom schemes and then repeatedly uses
  only their consequences in a model.  Packaging those consequences directly
  keeps downstream reductions independent of a particular proof calculus while
  retaining the exact numeral arithmetic and finite-interval content.
*)

From Stdlib Require Import Arith.PeanoNat Lia Logic.Classical_Prop
  Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Quantifier Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Eq Operator Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import
  ModelTheory RewriteClosure Semantics OperatorSemantics Elementary.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Misc Syntax Model Hierarchy.

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

Definition r0_empty_bound_env {A} : Fin.t 0 -> A :=
  fun i => Fin.case0 (fun _ => A) i.

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

(** * Sigma-one truth transport *)

Theorem r0_semiterm_val_numeral : forall M X n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall (t : semiterm oring_language X n)
         (bv : Fin.t n -> nat) (fv : X -> nat),
  semiterm_val Str
      (fun i => oring_numeral O (bv i))
      (fun x => oring_numeral O (fv x)) t =
  oring_numeral O (semiterm_val nat_standard_structure bv fv t).
Proof.
  intros M X n Str O Horing Hr0 t.
  pose proof (oring_standard_structure_unique Horing) as HStr. subst Str.
  induction t as [i | x | k F v IH]; intros bv fv;
    cbn [semiterm_val oring_standard_structure nat_standard_structure].
  - reflexivity.
  - reflexivity.
  - destruct F.
    + reflexivity.
    + reflexivity.
    + change
        (oring_add O
           (semiterm_val (oring_standard_structure O)
             (fun i => oring_numeral O (bv i))
             (fun x => oring_numeral O (fv x)) (v Fin.F1))
           (semiterm_val (oring_standard_structure O)
             (fun i => oring_numeral O (bv i))
             (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1))) =
         oring_numeral O
           (Nat.add
             (semiterm_val nat_standard_structure bv fv (v Fin.F1))
             (semiterm_val nat_standard_structure bv fv
               (v (Fin.FS Fin.F1))))).
      rewrite (IH Fin.F1 bv fv), (IH (Fin.FS Fin.F1) bv fv).
      exact (r0_numeral_add Hr0 _ _).
    + change
        (oring_mul O
           (semiterm_val (oring_standard_structure O)
             (fun i => oring_numeral O (bv i))
             (fun x => oring_numeral O (fv x)) (v Fin.F1))
           (semiterm_val (oring_standard_structure O)
             (fun i => oring_numeral O (bv i))
             (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1))) =
         oring_numeral O
           (Nat.mul
             (semiterm_val nat_standard_structure bv fv (v Fin.F1))
             (semiterm_val nat_standard_structure bv fv
               (v (Fin.FS Fin.F1))))).
      rewrite (IH Fin.F1 bv fv), (IH (Fin.FS Fin.F1) bv fv).
      exact (r0_numeral_mul Hr0 _ _).
Qed.

Lemma r0_numeral_fin_env_cons : forall M n (O : oring_carrier M)
    (x : nat) (bv : Fin.t n -> nat),
  (fun i => oring_numeral O (fin_env_cons x bv i)) =
  fin_env_cons (oring_numeral O x) (fun i => oring_numeral O (bv i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    oring_numeral O (fin_env_cons x bv j) =
    fin_env_cons (oring_numeral O x)
      (fun q => oring_numeral O (bv q)) j) eq_refl _).
  intros q. reflexivity.
Qed.

Lemma r0_positive_atom_transport : forall M X n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall k (r : language_rel oring_language k)
         (v : Fin.t k -> semiterm oring_language X n)
         (bv : Fin.t n -> nat) (fv : X -> nat),
  semiformula_eval nat_standard_structure bv fv (Semiformula_rel r v) ->
  semiformula_eval Str
    (fun i => oring_numeral O (bv i))
    (fun x => oring_numeral O (fv x)) (Semiformula_rel r v).
Proof.
  intros M X n Str O Horing Hr0 k r v bv fv H.
  pose proof (oring_standard_structure_unique Horing) as HStr. subst Str.
  destruct r.
  - change
      (semiterm_val nat_standard_structure bv fv (v Fin.F1) =
       semiterm_val nat_standard_structure bv fv (v (Fin.FS Fin.F1))) in H.
    change
      (semiterm_val (oring_standard_structure O)
         (fun i => oring_numeral O (bv i))
         (fun x => oring_numeral O (fv x)) (v Fin.F1) =
       semiterm_val (oring_standard_structure O)
         (fun i => oring_numeral O (bv i))
         (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1))).
    repeat rewrite (r0_semiterm_val_numeral
      (oring_standard_structure_interprets O) Hr0).
    now rewrite H.
  - change
      (Nat.lt
        (semiterm_val nat_standard_structure bv fv (v Fin.F1))
        (semiterm_val nat_standard_structure bv fv (v (Fin.FS Fin.F1)))) in H.
    change
      (oring_lt O
        (semiterm_val (oring_standard_structure O)
          (fun i => oring_numeral O (bv i))
          (fun x => oring_numeral O (fv x)) (v Fin.F1))
        (semiterm_val (oring_standard_structure O)
          (fun i => oring_numeral O (bv i))
          (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1)))).
    repeat rewrite (r0_semiterm_val_numeral
      (oring_standard_structure_interprets O) Hr0).
    apply (proj2 (r0_numeral_lt_iff Hr0 _ _)). exact H.
Qed.

Lemma r0_negative_atom_transport : forall M X n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall k (r : language_rel oring_language k)
         (v : Fin.t k -> semiterm oring_language X n)
         (bv : Fin.t n -> nat) (fv : X -> nat),
  semiformula_eval nat_standard_structure bv fv (Semiformula_nrel r v) ->
  semiformula_eval Str
    (fun i => oring_numeral O (bv i))
    (fun x => oring_numeral O (fv x)) (Semiformula_nrel r v).
Proof.
  intros M X n Str O Horing Hr0 k r v bv fv H.
  pose proof (oring_standard_structure_unique Horing) as HStr. subst Str.
  destruct r.
  - change
      (semiterm_val nat_standard_structure bv fv (v Fin.F1) <>
       semiterm_val nat_standard_structure bv fv (v (Fin.FS Fin.F1))) in H.
    change
      (semiterm_val (oring_standard_structure O)
         (fun i => oring_numeral O (bv i))
         (fun x => oring_numeral O (fv x)) (v Fin.F1) <>
       semiterm_val (oring_standard_structure O)
         (fun i => oring_numeral O (bv i))
         (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1))).
    repeat rewrite (r0_semiterm_val_numeral
      (oring_standard_structure_interprets O) Hr0).
    intro Heq. apply H.
    now apply (proj1 (r0_numeral_eq_iff Hr0 _ _)) in Heq.
  - change
      (~ Nat.lt
        (semiterm_val nat_standard_structure bv fv (v Fin.F1))
        (semiterm_val nat_standard_structure bv fv (v (Fin.FS Fin.F1)))) in H.
    change
      (~ oring_lt O
        (semiterm_val (oring_standard_structure O)
          (fun i => oring_numeral O (bv i))
          (fun x => oring_numeral O (fv x)) (v Fin.F1))
        (semiterm_val (oring_standard_structure O)
          (fun i => oring_numeral O (bv i))
          (fun x => oring_numeral O (fv x)) (v (Fin.FS Fin.F1)))).
    repeat rewrite (r0_semiterm_val_numeral
      (oring_standard_structure_interprets O) Hr0).
    intro Hlt. apply H.
    now apply (proj1 (r0_numeral_lt_iff Hr0 _ _)) in Hlt.
Qed.

Theorem r0_sigma_one_eval_transport : forall M X
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall n (p : semiformula oring_language X n),
  arithmetic_hierarchy X arithmetic_sigma 1 n p ->
  forall (bv : Fin.t n -> nat) (fv : X -> nat),
  semiformula_eval nat_standard_structure bv fv p ->
  semiformula_eval Str
    (fun i => oring_numeral O (bv i))
    (fun x => oring_numeral O (fv x)) p.
Proof.
  intros M X Str O Horing Hr0.
  set (P := fun n (p : semiformula oring_language X n) =>
    forall (bv : Fin.t n -> nat) (fv : X -> nat),
      semiformula_eval nat_standard_structure bv fv p ->
      semiformula_eval Str
        (fun i => oring_numeral O (bv i))
        (fun x => oring_numeral O (fv x)) p).
  assert (Hverum : forall n, P n (Semiformula_verum n)).
  { intros n bv fv _. exact I. }
  assert (Hfalsum : forall n, P n (Semiformula_falsum n)).
  { intros n bv fv H. exact H. }
  assert (Hrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_rel r v)).
  { intros n k r v bv fv H.
    exact (@r0_positive_atom_transport M X n Str O Horing Hr0
      k r v bv fv H). }
  assert (Hnrel : forall n k (r : language_rel oring_language k)
      (v : Fin.t k -> semiterm oring_language X n),
      P n (Semiformula_nrel r v)).
  { intros n k r v bv fv H.
    exact (@r0_negative_atom_transport M X n Str O Horing Hr0
      k r v bv fv H). }
  assert (Hand : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_and p q)).
  { intros n p q _ _ IHp IHq bv fv [Hp Hq].
    split; [now apply IHp | now apply IHq]. }
  assert (Hor : forall n (p q : semiformula oring_language X n),
      arithmetic_hierarchy X arithmetic_sigma 1 n p ->
      arithmetic_hierarchy X arithmetic_sigma 1 n q ->
      P n p -> P n q -> P n (Semiformula_or p q)).
  { intros n p q _ _ IHp IHq bv fv [Hp | Hq].
    - left. now apply IHp.
    - right. now apply IHq. }
  assert (Hball : forall n (t : semiterm oring_language X n)
      (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p ->
      P n (semiformula_ball_lt arithmetic_lt_operator t p)).
  { unfold P.
    intros n t p _ IHp bv fv Hnat.
    rewrite semiformula_eval_ball_lt in Hnat.
    rewrite semiformula_eval_ball_lt.
    setoid_rewrite (structure_relation_operator
      (structure_oring_lt nat_standard_structure_interprets)) in Hnat.
    unfold arithmetic_lt_operator.
    rewrite (r0_semiterm_val_numeral Horing Hr0 t bv fv).
    intros x Hx.
    apply (proj1 (structure_relation_operator
      (structure_oring_lt Horing) x
      (oring_numeral O (semiterm_val nat_standard_structure bv fv t)))) in Hx.
    destruct (proj1 (r0_lt_numeral Hr0 _ _) Hx) as [i [Hi Hxi]].
    subst x.
    pose proof (IHp (fin_env_cons i bv) fv (Hnat i Hi)) as Hp.
    rewrite (r0_numeral_fin_env_cons O i bv) in Hp. exact Hp. }
  assert (Hexists : forall n (p : semiformula oring_language X (S n)),
      arithmetic_hierarchy X arithmetic_sigma 1 (S n) p ->
      P (S n) p -> P n (Semiformula_exists p)).
  { intros n p _ IHp bv fv [i Hi].
    exists (oring_numeral O i).
    pose proof (IHp (fin_env_cons i bv) fv Hi) as Hp.
    rewrite (r0_numeral_fin_env_cons O i bv) in Hp. exact Hp. }
  intros n p Hp.
  exact (arithmetic_sigma_one_induction Hverum Hfalsum Hrel Hnrel
    Hand Hor Hball Hexists Hp).
Qed.

(** Pi-one truth reflects along the same numeral embedding.  Factoring this
    valuation-parametric dual avoids repeating the sentence-only classical
    contraposition in every absoluteness client. *)
Theorem r0_pi_one_eval_reflection : forall M X
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall n (p : semiformula oring_language X n),
  arithmetic_hierarchy X arithmetic_pi 1 n p ->
  forall (bv : Fin.t n -> nat) (fv : X -> nat),
  semiformula_eval Str
    (fun i => oring_numeral O (bv i))
    (fun x => oring_numeral O (fv x)) p ->
  semiformula_eval nat_standard_structure bv fv p.
Proof.
  intros M X Str O Horing Hr0 n p Hp bv fv HM.
  apply NNPP. intro Hnat.
  assert (Hneg_hierarchy :
      arithmetic_hierarchy X arithmetic_sigma 1 n (semiformula_neg p)).
  { exact (arithmetic_hierarchy_neg Hp). }
  assert (Hneg_nat :
      semiformula_eval nat_standard_structure bv fv (semiformula_neg p)).
  { rewrite semiformula_eval_neg. exact Hnat. }
  pose proof (@r0_sigma_one_eval_transport M X Str O Horing Hr0
    n (semiformula_neg p) Hneg_hierarchy bv fv Hneg_nat) as Hneg_M.
  rewrite semiformula_eval_neg in Hneg_M.
  exact (Hneg_M HM).
Qed.

(** Sigma-one truth in the standard natural-number structure is upward
    absolute to every structure satisfying the concrete R0 laws. *)
Theorem r0_sigma_one_model_complete : forall M
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall sigma : sentence oring_language,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
    sentence_realize nat_standard_structure sigma ->
    sentence_realize Str sigma.
Proof.
  intros M Str O Horing Hr0 sigma Hsigma Hnat.
  unfold sentence_realize, formula_eval in Hnat.
  unfold sentence_realize, formula_eval.
  match type of Hnat with
  | semiformula_eval _ ?bv ?fv _ =>
      pose proof (@r0_sigma_one_eval_transport M Empty_set Str O Horing Hr0
        0 sigma Hsigma bv fv Hnat) as H;
      match goal with
      | |- semiformula_eval _ ?tb ?tf _ =>
          assert (Hbound : forall i : Fin.t 0,
            oring_numeral O (bv i) = tb i);
          [intro i; exact (Fin.case0 (fun j =>
             oring_numeral O (bv j) = tb j) i)|];
          apply (proj1 (@semiformula_eval_bound_extensional
            oring_language M Empty_set 0 Str
            (fun i : Fin.t 0 => oring_numeral O (bv i)) tb
            (fun x : Empty_set => oring_numeral O (fv x)) sigma Hbound)) in H;
          assert (Hfree : forall x : Empty_set,
            semiformula_free_occurs x sigma ->
            oring_numeral O (fv x) = tf x);
          [intros x _; destruct x|];
          apply (proj1 (@semiformula_eval_free_ext
            oring_language M Empty_set 0 Str tb
            (fun x : Empty_set => oring_numeral O (fv x)) tf sigma Hfree)) in H;
          exact H
      end
  end.
Qed.

(** The parameter-free variant used by later definability developments. *)
Corollary r0_sigma_one_semisentence_transport : forall M n
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall sigma : semiformula oring_language Empty_set n,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 n sigma ->
    forall bv : Fin.t n -> nat,
      semiformula_eval nat_standard_structure bv (@r0_empty_free_env nat) sigma ->
      semiformula_eval Str (fun i => oring_numeral O (bv i))
        (@r0_empty_free_env M) sigma.
Proof.
  intros M n Str O Horing Hr0 sigma Hsigma bv Hnat.
  pose proof (@r0_sigma_one_eval_transport M Empty_set Str O Horing Hr0
    n sigma Hsigma bv (@r0_empty_free_env nat) Hnat) as H.
  assert (Hfree : forall x : Empty_set,
      semiformula_free_occurs x sigma ->
      oring_numeral O (@r0_empty_free_env nat x) =
      @r0_empty_free_env M x).
  { intros x _. destruct x. }
  apply (proj1 (@semiformula_eval_free_ext
    oring_language M Empty_set n Str
    (fun i => oring_numeral O (bv i))
    (fun x => oring_numeral O (@r0_empty_free_env nat x))
    (@r0_empty_free_env M) sigma Hfree)) in H.
  exact H.
Qed.

(** Dually, Pi-one truth reflects from an R0 structure back to the standard
    natural-number structure. *)
Theorem r0_pi_one_model_reflection : forall M
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall sigma : sentence oring_language,
    arithmetic_hierarchy Empty_set arithmetic_pi 1 0 sigma ->
    sentence_realize Str sigma ->
    sentence_realize nat_standard_structure sigma.
Proof.
  intros M Str O Horing Hr0 sigma Hsigma HM.
  apply NNPP. intro Hnat.
  assert (Hneg_sigma : arithmetic_hierarchy Empty_set arithmetic_sigma 1 0
      (semiformula_neg sigma)).
  { pose proof (arithmetic_hierarchy_neg Hsigma) as Hneg.
    exact Hneg. }
  assert (Hneg_nat : sentence_realize nat_standard_structure
      (semiformula_neg sigma)).
  { unfold sentence_realize, formula_eval in Hnat.
    unfold sentence_realize, formula_eval.
    rewrite semiformula_eval_neg. exact Hnat. }
  pose proof (r0_sigma_one_model_complete Horing Hr0 Hneg_sigma Hneg_nat)
    as Hneg_M.
  unfold sentence_realize, formula_eval in Hneg_M.
  rewrite semiformula_eval_neg in Hneg_M.
  exact (Hneg_M HM).
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

(** Every true Sigma-one sentence is already provable in R0, and therefore
    in every syntactic extension of R0. *)
Theorem r0_sigma_one_proof_complete : forall
    (T : theory oring_language) (sigma : sentence oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
  first_order_model_realize nat_standard_model sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros T sigma Hweak Hsigma Hnat.
  apply (generic_weaker_subset Hweak sigma).
  apply r0_proof_complete.
  intros m O Horing Hr0.
  unfold first_order_model_realize in Hnat |-.
  exact (r0_sigma_one_model_complete Horing Hr0 Hsigma Hnat).
Qed.

(** On Sigma-one sentences, standard truth and provability coincide for any
    Sigma-one-sound extension of R0. *)
Theorem r0_sigma_one_provable_iff : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall sigma : sentence oring_language,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
    (first_order_model_realize nat_standard_model sigma <->
     first_order_theory_provable T sigma).
Proof.
  intros T Hweak Hsound sigma Hsigma. split.
  - now apply (r0_sigma_one_proof_complete Hweak Hsigma).
  - intro Hproof.
    exact (arithmetic_theory_sound_on_hierarchy_elim
      Hsound Hproof Hsigma).
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
