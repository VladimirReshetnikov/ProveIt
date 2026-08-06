(**
  Sigma-one, Pi-one, and Delta-one absoluteness over models of Cobham R0.

  Foundation states the principal results for semisentences in models of
  PA-minus.  The proofs use only the numeral behavior supplied by R0.  We
  therefore expose a stronger valuation-parametric core for arbitrary free
  variables and recover the source-facing closed-definition interface as
  corollaries.
*)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics ModelTheory.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Hierarchy Misc Model Syntax.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Hierarchy Definable.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma arithmetic_empty_valuation_unique : forall (A : Type)
    (f g : Empty_set -> A), f = g.
Proof.
  intros A f g. apply functional_extensionality. intros [].
Qed.

(** Sigma-one truth is upward absolute along the numeral embedding of every
    R0 carrier.  This is deliberately more general than the source theorem:
    free parameters need not be closed into numeral terms first. *)
Theorem arithmetic_sigma_one_upward_absolute : forall M X
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
  intros. now apply (r0_sigma_one_eval_transport H H0 H1).
Qed.

(** Pi-one truth is downward absolute along the same embedding. *)
Theorem arithmetic_pi_one_downward_absolute : forall M X
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
  intros. now apply (r0_pi_one_eval_reflection H H0 H1).
Qed.

(** Delta-zero formulas are absolute.  The reverse implication views the
    same formula as Pi-one, using polarity-independence at level zero. *)
Theorem arithmetic_sigma_zero_absolute : forall M X
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall n (p : semiformula oring_language X n),
    arithmetic_hierarchy X arithmetic_sigma 0 n p ->
    forall (bv : Fin.t n -> nat) (fv : X -> nat),
      (semiformula_eval nat_standard_structure bv fv p <->
       semiformula_eval Str
         (fun i => oring_numeral O (bv i))
         (fun x => oring_numeral O (fv x)) p).
Proof.
  intros M X Str O Horing Hr0 n p Hp bv fv. split.
  - apply (arithmetic_sigma_one_upward_absolute Horing Hr0
      (arithmetic_hierarchy_of_zero Hp arithmetic_sigma 1)).
  - apply (arithmetic_pi_one_downward_absolute Horing Hr0
      (arithmetic_hierarchy_of_zero Hp arithmetic_pi 1)).
Qed.

(** Delta-one formulas carry Sigma and Pi presentations.  Properness in the
    two structures turns the one-way absoluteness results into an equivalence. *)
Theorem arithmetic_delta_one_absolute : forall M X
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall n
    (p : arithmetic_sorted_formula X n (arithmetic_delta_symbol 1))
    (fv : X -> nat),
  arithmetic_sorted_delta_proper nat_standard_structure fv p ->
  arithmetic_sorted_delta_proper Str
    (fun x => oring_numeral O (fv x)) p ->
  forall bv : Fin.t n -> nat,
    (semiformula_eval nat_standard_structure bv fv
       (arithmetic_sorted_formula_val p) <->
     semiformula_eval Str
       (fun i => oring_numeral O (bv i))
       (fun x => oring_numeral O (fv x))
       (arithmetic_sorted_formula_val p)).
Proof.
  intros M X Str O Horing Hr0 n p fv Hproper_nat Hproper bv. split.
  - apply (arithmetic_sigma_one_upward_absolute Horing Hr0
      (arithmetic_sorted_sigma_prop
        (arithmetic_sorted_delta_sigma p))).
  - intro HM.
    apply (proj2 (Hproper_nat bv)).
    apply (arithmetic_pi_one_downward_absolute Horing Hr0
      (arithmetic_sorted_pi_prop (arithmetic_sorted_delta_pi p))).
    now apply (proj1 (Hproper (fun i => oring_numeral O (bv i)))).
Qed.

(** Source-facing semisentence specializations. *)
Corollary arithmetic_sigma_one_semisentence_upward_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall p : semiformula oring_language Empty_set n,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 n p ->
    forall bv : Fin.t n -> nat,
      semiformula_eval nat_standard_structure bv
        (@r0_empty_free_env nat) p ->
      semiformula_eval Str (fun i => oring_numeral O (bv i))
        (@r0_empty_free_env M) p.
Proof.
  intros M n Str O Horing Hr0 p Hp bv Hnat.
  pose proof (@arithmetic_sigma_one_upward_absolute
    M Empty_set Str O Horing Hr0 n p Hp
    bv (@r0_empty_free_env nat) Hnat) as HM.
  assert (Hempty :
      (fun x : Empty_set => oring_numeral O (@r0_empty_free_env nat x)) =
      @r0_empty_free_env M).
  { apply arithmetic_empty_valuation_unique. }
  now rewrite Hempty in HM.
Qed.

Corollary arithmetic_pi_one_semisentence_downward_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall p : semiformula oring_language Empty_set n,
    arithmetic_hierarchy Empty_set arithmetic_pi 1 n p ->
    forall bv : Fin.t n -> nat,
      semiformula_eval Str (fun i => oring_numeral O (bv i))
        (@r0_empty_free_env M) p ->
      semiformula_eval nat_standard_structure bv
        (@r0_empty_free_env nat) p.
Proof.
  intros M n Str O Horing Hr0 p Hp bv HM.
  assert (Hempty :
      (fun x : Empty_set => oring_numeral O (@r0_empty_free_env nat x)) =
      @r0_empty_free_env M).
  { apply arithmetic_empty_valuation_unique. }
  rewrite <- Hempty in HM.
  exact (@arithmetic_pi_one_downward_absolute
    M Empty_set Str O Horing Hr0 n p Hp
    bv (@r0_empty_free_env nat) HM).
Qed.

Corollary arithmetic_sigma_zero_semisentence_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall p : semiformula oring_language Empty_set n,
    arithmetic_hierarchy Empty_set arithmetic_sigma 0 n p ->
    forall bv : Fin.t n -> nat,
      (semiformula_eval nat_standard_structure bv
         (@r0_empty_free_env nat) p <->
       semiformula_eval Str (fun i => oring_numeral O (bv i))
         (@r0_empty_free_env M) p).
Proof.
  intros M n Str O Horing Hr0 p Hp bv.
  pose proof (@arithmetic_sigma_zero_absolute
    M Empty_set Str O Horing Hr0 n p Hp
    bv (@r0_empty_free_env nat)) as Hiff.
  assert (Hempty :
      (fun x : Empty_set => oring_numeral O (@r0_empty_free_env nat x)) =
      @r0_empty_free_env M).
  { apply arithmetic_empty_valuation_unique. }
  now rewrite Hempty in Hiff.
Qed.

Corollary arithmetic_delta_one_semisentence_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall p : arithmetic_sorted_formula Empty_set n
      (arithmetic_delta_symbol 1),
  arithmetic_sorted_delta_proper_on nat_standard_structure p ->
  arithmetic_sorted_delta_proper_on Str p ->
  forall bv : Fin.t n -> nat,
    (semiformula_eval nat_standard_structure bv
       (@r0_empty_free_env nat) (arithmetic_sorted_formula_val p) <->
     semiformula_eval Str (fun i => oring_numeral O (bv i))
       (@r0_empty_free_env M) (arithmetic_sorted_formula_val p)).
Proof.
  intros M n Str O Horing Hr0 p Hproper_nat Hproper bv.
  assert (Hempty :
      (fun x : Empty_set => oring_numeral O (@r0_empty_free_env nat x)) =
      @r0_empty_free_env M).
  { apply arithmetic_empty_valuation_unique. }
  pose proof (@arithmetic_delta_one_absolute
    M Empty_set Str O Horing Hr0 n p
    (@r0_empty_free_env nat) Hproper_nat) as Habsolute.
  rewrite Hempty in Habsolute.
  exact (Habsolute Hproper bv).
Qed.

(** A relation defined by one proper Delta-one formula has the same truth
    value on naturals and on their numeral images in every R0 carrier. *)
Theorem arithmetic_delta_one_defined_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall (Rnat : (Fin.t n -> nat) -> Prop)
         (R : (Fin.t n -> M) -> Prop)
         (p : arithmetic_sorted_formula Empty_set n
           (arithmetic_delta_symbol 1)),
  arithmetic_sorted_defined nat_standard_structure Rnat p ->
  arithmetic_sorted_defined Str R p ->
  forall bv : Fin.t n -> nat,
    (Rnat bv <-> R (fun i => oring_numeral O (bv i))).
Proof.
  intros M n Str O Horing Hr0 Rnat R p Hnat HM bv.
  rewrite <- (arithmetic_sorted_defined_iff Hnat bv).
  rewrite <- (arithmetic_sorted_defined_iff HM
    (fun i => oring_numeral O (bv i))).
  apply (arithmetic_delta_one_semisentence_absolute Horing Hr0
    (arithmetic_sorted_defined_delta_proper Hnat)
    (arithmetic_sorted_defined_delta_proper HM)).
Qed.

Theorem arithmetic_sigma_zero_defined_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall (Rnat : (Fin.t n -> nat) -> Prop)
         (R : (Fin.t n -> M) -> Prop)
         (p : arithmetic_sorted_formula Empty_set n
           arithmetic_sigma_zero_symbol),
  arithmetic_sorted_defined nat_standard_structure Rnat p ->
  arithmetic_sorted_defined Str R p ->
  forall bv : Fin.t n -> nat,
    (Rnat bv <-> R (fun i => oring_numeral O (bv i))).
Proof.
  intros M n Str O Horing Hr0 Rnat R p Hnat HM bv.
  rewrite <- (arithmetic_sorted_defined_iff Hnat bv).
  rewrite <- (arithmetic_sorted_defined_iff HM
    (fun i => oring_numeral O (bv i))).
  apply (arithmetic_sigma_zero_semisentence_absolute Horing Hr0).
  exact (arithmetic_sorted_sigma_prop p).
Qed.

(** Functional absoluteness follows from graph absoluteness.  Requiring the
    same proper Delta-one graph is the proof-relevant Coq counterpart of the
    source's two [DefinedFunction] instances. *)
Theorem arithmetic_delta_one_defined_function_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall (fnat : (Fin.t n -> nat) -> nat)
         (f : (Fin.t n -> M) -> M)
         (p : arithmetic_sorted_formula Empty_set (S n)
           (arithmetic_delta_symbol 1)),
  arithmetic_sorted_defined_function nat_standard_structure fnat p ->
  arithmetic_sorted_defined_function Str f p ->
  forall bv : Fin.t n -> nat,
    oring_numeral O (fnat bv) =
    f (fun i => oring_numeral O (bv i)).
Proof.
  intros M n Str O Horing Hr0 fnat f p Hnat HM bv.
  pose proof (@arithmetic_delta_one_defined_absolute M (S n) Str O
    Horing Hr0
    (fun v => v Fin.F1 = fnat (fun i => v (Fin.FS i)))
    (fun v => v Fin.F1 = f (fun i => v (Fin.FS i)))
    p Hnat HM (fin_env_cons (fnat bv) bv)) as Hgraph.
  apply (proj1 Hgraph).
  reflexivity.
Qed.

Theorem arithmetic_sigma_zero_defined_function_absolute : forall M n
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  forall (fnat : (Fin.t n -> nat) -> nat)
         (f : (Fin.t n -> M) -> M)
         (p : arithmetic_sorted_formula Empty_set (S n)
           arithmetic_sigma_zero_symbol),
  arithmetic_sorted_defined_function nat_standard_structure fnat p ->
  arithmetic_sorted_defined_function Str f p ->
  forall bv : Fin.t n -> nat,
    oring_numeral O (fnat bv) =
    f (fun i => oring_numeral O (bv i)).
Proof.
  intros M n Str O Horing Hr0 fnat f p Hnat HM bv.
  pose proof (@arithmetic_sigma_zero_defined_absolute M (S n) Str O
    Horing Hr0
    (fun v => v Fin.F1 = fnat (fun i => v (Fin.FS i)))
    (fun v => v Fin.F1 = f (fun i => v (Fin.FS i)))
    p Hnat HM (fin_env_cons (fnat bv) bv)) as Hgraph.
  apply (proj1 Hgraph).
  reflexivity.
Qed.

(** * Numeral instances and parameterized Sigma-one completeness *)

Definition arithmetic_numeral_instance {n}
    (p : semiformula oring_language Empty_set n)
    (bv : Fin.t n -> nat) : sentence oring_language :=
  semiformula_substitute
    (fun i => @arithmetic_numeral_term Empty_set 0 (bv i)) p.

Lemma arithmetic_numeral_instance_hierarchy : forall pol level n
    (p : semiformula oring_language Empty_set n)
    (bv : Fin.t n -> nat),
  arithmetic_hierarchy Empty_set pol level n p ->
  arithmetic_hierarchy Empty_set pol level 0
    (arithmetic_numeral_instance p bv).
Proof.
  intros pol level n p bv Hp.
  unfold arithmetic_numeral_instance, semiformula_substitute.
  exact (arithmetic_hierarchy_rewrite Hp
    (rew_subst (fun i => @arithmetic_numeral_term Empty_set 0 (bv i)))).
Qed.

Lemma arithmetic_numeral_instance_realize_iff_in_structure : forall M
    (Str : first_order_structure oring_language M) (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  forall n (p : semiformula oring_language Empty_set n)
    (bv : Fin.t n -> nat),
  sentence_realize Str (arithmetic_numeral_instance p bv) <->
  semiformula_eval Str (fun i => oring_numeral O (bv i))
    (@r0_empty_free_env M) p.
Proof.
  intros M Str O Horing n p bv.
  unfold sentence_realize, formula_eval, arithmetic_numeral_instance,
    semiformula_substitute.
  rewrite semiformula_eval_rewrite.
  match goal with
  | |- semiformula_eval _ ?b ?f _ <-> _ =>
      assert (Hbound :
        b = (fun i => oring_numeral O (bv i)));
      [apply functional_extensionality; intro i;
       rewrite rew_subst_bvar;
       apply (@arithmetic_numeral_term_val M Empty_set 0
         Str _ _ O (bv i) Horing)|];
      assert (Hfree : f = @r0_empty_free_env M);
      [apply arithmetic_empty_valuation_unique|];
      rewrite Hbound, Hfree; reflexivity
  end.
Qed.

Lemma arithmetic_numeral_instance_realize_iff : forall n
    (p : semiformula oring_language Empty_set n)
    (bv : Fin.t n -> nat),
  first_order_model_realize nat_standard_model
    (arithmetic_numeral_instance p bv) <->
  semiformula_eval nat_standard_structure bv
    (@r0_empty_free_env nat) p.
Proof.
  intros n p bv.
  unfold first_order_model_realize, sentence_realize, formula_eval,
    arithmetic_numeral_instance, semiformula_substitute.
  rewrite semiformula_eval_rewrite.
  match goal with
  | |- semiformula_eval _ ?b ?f _ <-> _ =>
      assert (Hbound : b = bv);
      [apply functional_extensionality; intro i;
       rewrite rew_subst_bvar;
       rewrite (@arithmetic_numeral_term_val nat Empty_set 0
         nat_standard_structure _ _ nat_oring_carrier (bv i)
         nat_standard_structure_interprets);
       apply nat_oring_numeral|];
      assert (Hfree : f = @r0_empty_free_env nat);
      [apply arithmetic_empty_valuation_unique|];
      rewrite Hbound, Hfree; reflexivity
  end.
Qed.

(** Foundation's parameterized completeness theorem, generalized from
    PA-minus extensions to arbitrary proof-theoretic extensions of R0. *)
Theorem arithmetic_sigma_one_provable_iff_with_numeral_parameters : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall n (p : semiformula oring_language Empty_set n),
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 n p ->
    forall bv : Fin.t n -> nat,
      (semiformula_eval nat_standard_structure bv
         (@r0_empty_free_env nat) p <->
       first_order_theory_provable T (arithmetic_numeral_instance p bv)).
Proof.
  intros T Hweak Hsound n p Hp bv.
  rewrite <- (arithmetic_numeral_instance_realize_iff p bv).
  apply (r0_sigma_one_provable_iff Hweak Hsound).
  exact (arithmetic_numeral_instance_hierarchy bv Hp).
Qed.

Theorem arithmetic_sigma_zero_model_iff_provable_with_numeral_parameters :
  forall M (Str : first_order_structure oring_language M)
    (O : oring_carrier M) (T : theory oring_language),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall n (p : semiformula oring_language Empty_set n),
    arithmetic_hierarchy Empty_set arithmetic_sigma 0 n p ->
    forall bv : Fin.t n -> nat,
      (semiformula_eval Str (fun i => oring_numeral O (bv i))
         (@r0_empty_free_env M) p <->
       first_order_theory_provable T (arithmetic_numeral_instance p bv)).
Proof.
  intros M Str O T Horing Hr0 Hweak Hsound n p Hp bv.
  transitivity (semiformula_eval nat_standard_structure bv
    (@r0_empty_free_env nat) p).
  - symmetry. apply (arithmetic_sigma_zero_semisentence_absolute Horing Hr0 Hp).
  - apply (arithmetic_sigma_one_provable_iff_with_numeral_parameters
      Hweak Hsound).
    exact (arithmetic_hierarchy_of_zero Hp arithmetic_sigma 1).
Qed.

Theorem arithmetic_delta_one_model_iff_provable_with_numeral_parameters :
  forall M (Str : first_order_structure oring_language M)
    (O : oring_carrier M) (T : theory oring_language),
  structure_interprets_oring Str oring_language_structure O ->
  r0_laws O ->
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall n
    (p : arithmetic_sorted_formula Empty_set n (arithmetic_delta_symbol 1)),
  arithmetic_sorted_delta_proper_on nat_standard_structure p ->
  arithmetic_sorted_delta_proper_on Str p ->
  forall bv : Fin.t n -> nat,
    (semiformula_eval Str (fun i => oring_numeral O (bv i))
       (@r0_empty_free_env M) (arithmetic_sorted_formula_val p) <->
     first_order_theory_provable T
       (arithmetic_numeral_instance (arithmetic_sorted_formula_val p) bv)).
Proof.
  intros M Str O T Horing Hr0 Hweak Hsound n p Hproper_nat Hproper bv.
  transitivity (semiformula_eval nat_standard_structure bv
    (@r0_empty_free_env nat) (arithmetic_sorted_formula_val p)).
  - symmetry. apply (arithmetic_delta_one_semisentence_absolute Horing Hr0
      Hproper_nat Hproper).
  - apply (arithmetic_sigma_one_provable_iff_with_numeral_parameters
      Hweak Hsound).
    exact (arithmetic_sorted_sigma_prop (arithmetic_sorted_delta_sigma p)).
Qed.
