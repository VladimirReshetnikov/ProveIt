(** Internal recognition of first-order language symbols.

    This begins the concrete bootstrapping stack used by standard
    provability.  Foundation packages two Delta-zero arithmetic formulas
    recognizing the ranges of the function- and relation-symbol encodings.
    The Coq port keeps the formula and hierarchy certificate explicit and
    reuses the verified encodings from [Basic/Coding]. *)

From Stdlib Require Import Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Operator Coding.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Misc Syntax Model Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition boot_empty_nat_env (x : Empty_set) : nat := match x with end.

Definition language_func_code_valid {L : language}
    (EL : language_encodable L) (k c : nat) : Prop :=
  exists f : language_func L k,
    encode (language_func_encoding EL k) f = c.

Definition language_rel_code_valid {L : language}
    (EL : language_encodable L) (k c : nat) : Prop :=
  exists r : language_rel L k,
    encode (language_rel_encoding EL k) r = c.

Record boot_language_lor_definable (L : language)
    (EL : language_encodable L) : Type := {
  boot_is_func_formula : arithmetic_semisentence 2;
  boot_is_rel_formula : arithmetic_semisentence 2;
  boot_is_func_delta_zero : arithmetic_delta_zero boot_is_func_formula;
  boot_is_rel_delta_zero : arithmetic_delta_zero boot_is_rel_formula;
  boot_is_func_standard : forall k c,
    language_func_code_valid EL k c <->
    semiformula_eval nat_standard_structure (fin_two k c)
      boot_empty_nat_env boot_is_func_formula;
  boot_is_rel_standard : forall k c,
    language_rel_code_valid EL k c <->
    semiformula_eval nat_standard_structure (fin_two k c)
      boot_empty_nat_env boot_is_rel_formula
}.

Arguments boot_language_lor_definable L EL : clear implicits.
Arguments boot_is_func_formula {L EL} _.
Arguments boot_is_rel_formula {L EL} _.

Definition boot_language_is_func {L EL M}
    (D : boot_language_lor_definable L EL)
    (Str : first_order_structure oring_language M) (k c : M) : Prop :=
  semiformula_eval Str (fin_two k c)
    (fun x : Empty_set => match x with end)
    (boot_is_func_formula D).

Definition boot_language_is_rel {L EL M}
    (D : boot_language_lor_definable L EL)
    (Str : first_order_structure oring_language M) (k c : M) : Prop :=
  semiformula_eval Str (fin_two k c)
    (fun x : Empty_set => match x with end)
    (boot_is_rel_formula D).

Lemma boot_language_is_func_def : forall L EL M
    (D : boot_language_lor_definable L EL)
    (Str : first_order_structure oring_language M) k c,
  boot_language_is_func D Str k c <->
  semiformula_eval Str (fin_two k c)
    (fun x : Empty_set => match x with end)
    (boot_is_func_formula D).
Proof. reflexivity. Qed.

Lemma boot_language_is_rel_def : forall L EL M
    (D : boot_language_lor_definable L EL)
    (Str : first_order_structure oring_language M) k c,
  boot_language_is_rel D Str k c <->
  semiformula_eval Str (fin_two k c)
    (fun x : Empty_set => match x with end)
    (boot_is_rel_formula D).
Proof. reflexivity. Qed.

Definition boot_func_quote {L : language} (EL : language_encodable L)
    {k} (f : language_func L k) : nat :=
  encode (language_func_encoding EL k) f.

Definition boot_rel_quote {L : language} (EL : language_encodable L)
    {k} (r : language_rel L k) : nat :=
  encode (language_rel_encoding EL k) r.

Lemma boot_func_quote_inj : forall L EL k
    (f g : language_func L k),
  boot_func_quote EL f = boot_func_quote EL g <-> f = g.
Proof.
  intros L EL k f g; split.
  - apply encoding_injective.
  - now intros ->.
Qed.

Lemma boot_rel_quote_inj : forall L EL k
    (r s : language_rel L k),
  boot_rel_quote EL r = boot_rel_quote EL s <-> r = s.
Proof.
  intros L EL k r s; split.
  - apply encoding_injective.
  - now intros ->.
Qed.

(** The two bound variables of a language-recognition formula are arity and
    code, respectively. *)
Definition boot_code_eq (i : Fin.t 2) (c : nat) :
    arithmetic_semisentence 2 :=
  arithmetic_eq_formula (Semiterm_bvar i) (arithmetic_numeral_term c).

Lemma boot_code_eq_delta_zero : forall i c,
  arithmetic_delta_zero (boot_code_eq i c).
Proof.
  intros i c. unfold boot_code_eq, arithmetic_delta_zero.
  apply arithmetic_hierarchy_eq.
Qed.

Lemma boot_code_eq_eval : forall (v : Fin.t 2 -> nat) i c,
  semiformula_eval nat_standard_structure v boot_empty_nat_env
    (boot_code_eq i c) <-> v i = c.
Proof.
  intros v i c. unfold boot_code_eq.
  rewrite (@arithmetic_eq_formula_eval nat Empty_set 2
    nat_standard_structure v boot_empty_nat_env nat_oring_carrier
    (Semiterm_bvar i) (arithmetic_numeral_term c)
    nat_standard_structure_interprets).
  simpl. rewrite (@arithmetic_numeral_term_val nat Empty_set 2
    nat_standard_structure v boot_empty_nat_env nat_oring_carrier c
    nat_standard_structure_interprets), nat_oring_numeral.
  reflexivity.
Qed.

Definition boot_oring_is_func_formula : arithmetic_semisentence 2 :=
  Semiformula_or
    (Semiformula_and (boot_code_eq Fin.F1 0)
      (boot_code_eq (Fin.FS Fin.F1) 0))
    (Semiformula_or
      (Semiformula_and (boot_code_eq Fin.F1 0)
        (boot_code_eq (Fin.FS Fin.F1) 1))
      (Semiformula_or
        (Semiformula_and (boot_code_eq Fin.F1 2)
          (boot_code_eq (Fin.FS Fin.F1) 2))
        (Semiformula_and (boot_code_eq Fin.F1 2)
          (boot_code_eq (Fin.FS Fin.F1) 3)))).

Definition boot_oring_is_rel_formula : arithmetic_semisentence 2 :=
  Semiformula_or
    (Semiformula_and (boot_code_eq Fin.F1 2)
      (boot_code_eq (Fin.FS Fin.F1) 0))
    (Semiformula_and (boot_code_eq Fin.F1 2)
      (boot_code_eq (Fin.FS Fin.F1) 1)).

Lemma boot_oring_is_func_delta_zero :
  arithmetic_delta_zero boot_oring_is_func_formula.
Proof.
  unfold boot_oring_is_func_formula.
  apply AH_or.
  - apply AH_and; apply boot_code_eq_delta_zero.
  - apply AH_or.
    + apply AH_and; apply boot_code_eq_delta_zero.
    + apply AH_or; apply AH_and; apply boot_code_eq_delta_zero.
Qed.

Lemma boot_oring_is_rel_delta_zero :
  arithmetic_delta_zero boot_oring_is_rel_formula.
Proof.
  unfold boot_oring_is_rel_formula.
  apply AH_or; apply AH_and; apply boot_code_eq_delta_zero.
Qed.

Lemma oring_func_code_valid_iff : forall k c,
  language_func_code_valid oring_language_encodable k c <->
  (k = 0 /\ c = 0) \/ (k = 0 /\ c = 1) \/
  (k = 2 /\ c = 2) \/ (k = 2 /\ c = 3).
Proof.
  intros k c; split.
  - intros [f Hf]. destruct f; simpl in Hf; subst c; tauto.
  - intros [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
    + now exists ORing_zero.
    + now exists ORing_one.
    + now exists ORing_add.
    + now exists ORing_mul.
Qed.

Lemma oring_rel_code_valid_iff : forall k c,
  language_rel_code_valid oring_language_encodable k c <->
  (k = 2 /\ c = 0) \/ (k = 2 /\ c = 1).
Proof.
  intros k c; split.
  - intros [r Hr]. destruct r; simpl in Hr; subst c; tauto.
  - intros [[-> ->] | [-> ->]].
    + now exists ORing_eq.
    + now exists ORing_lt.
Qed.

Lemma boot_oring_is_func_eval : forall k c,
  semiformula_eval nat_standard_structure (fin_two k c)
    boot_empty_nat_env boot_oring_is_func_formula <->
  (k = 0 /\ c = 0) \/ (k = 0 /\ c = 1) \/
  (k = 2 /\ c = 2) \/ (k = 2 /\ c = 3).
Proof.
  intros k c. unfold boot_oring_is_func_formula. simpl.
  repeat rewrite boot_code_eq_eval.
  reflexivity.
Qed.

Lemma boot_oring_is_rel_eval : forall k c,
  semiformula_eval nat_standard_structure (fin_two k c)
    boot_empty_nat_env boot_oring_is_rel_formula <->
  (k = 2 /\ c = 0) \/ (k = 2 /\ c = 1).
Proof.
  intros k c. unfold boot_oring_is_rel_formula. simpl.
  repeat rewrite boot_code_eq_eval.
  reflexivity.
Qed.

Definition oring_language_lor_definable :
    boot_language_lor_definable
      oring_language oring_language_encodable.
Proof.
  refine {| boot_is_func_formula := boot_oring_is_func_formula;
            boot_is_rel_formula := boot_oring_is_rel_formula;
            boot_is_func_delta_zero := boot_oring_is_func_delta_zero;
            boot_is_rel_delta_zero := boot_oring_is_rel_delta_zero |}.
  - intros k c. rewrite oring_func_code_valid_iff,
      boot_oring_is_func_eval. reflexivity.
  - intros k c. rewrite oring_rel_code_valid_iff,
      boot_oring_is_rel_eval. reflexivity.
Defined.

Definition boot_zero_index : nat := boot_func_quote
  oring_language_encodable ORing_zero.
Definition boot_one_index : nat := boot_func_quote
  oring_language_encodable ORing_one.
Definition boot_add_index : nat := boot_func_quote
  oring_language_encodable ORing_add.
Definition boot_mul_index : nat := boot_func_quote
  oring_language_encodable ORing_mul.
Definition boot_eq_index : nat := boot_rel_quote
  oring_language_encodable ORing_eq.
Definition boot_lt_index : nat := boot_rel_quote
  oring_language_encodable ORing_lt.

Lemma boot_oring_func_zero_index :
  language_func_code_valid oring_language_encodable 0 boot_zero_index.
Proof. now exists ORing_zero. Qed.
Lemma boot_oring_func_one_index :
  language_func_code_valid oring_language_encodable 0 boot_one_index.
Proof. now exists ORing_one. Qed.
Lemma boot_oring_func_add_index :
  language_func_code_valid oring_language_encodable 2 boot_add_index.
Proof. now exists ORing_add. Qed.
Lemma boot_oring_func_mul_index :
  language_func_code_valid oring_language_encodable 2 boot_mul_index.
Proof. now exists ORing_mul. Qed.
Lemma boot_oring_rel_eq_index :
  language_rel_code_valid oring_language_encodable 2 boot_eq_index.
Proof. now exists ORing_eq. Qed.
Lemma boot_oring_rel_lt_index :
  language_rel_code_valid oring_language_encodable 2 boot_lt_index.
Proof. now exists ORing_lt. Qed.

Lemma boot_zero_index_eq : boot_zero_index = 0. Proof. reflexivity. Qed.
Lemma boot_one_index_eq : boot_one_index = 1. Proof. reflexivity. Qed.
Lemma boot_add_index_eq : boot_add_index = 2. Proof. reflexivity. Qed.
Lemma boot_mul_index_eq : boot_mul_index = 3. Proof. reflexivity. Qed.
Lemma boot_eq_index_eq : boot_eq_index = 0. Proof. reflexivity. Qed.
Lemma boot_lt_index_eq : boot_lt_index = 1. Proof. reflexivity. Qed.
