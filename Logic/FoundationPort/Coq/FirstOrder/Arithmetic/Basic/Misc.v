(**
  Basic arithmetic syntax and semantics.

  This ports the mathematical surface of
  [Foundation/FirstOrder/Arithmetic/Basic/Misc.lean].  Ordered-ring carrier
  data and interpretation capabilities are explicit, so each theorem states
  only the operations it actually needs.
*)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record oring_carrier (M : Type) : Type := {
  oring_zero : M;
  oring_one : M;
  oring_add : M -> M -> M;
  oring_mul : M -> M -> M;
  oring_lt : M -> M -> Prop
}.

Arguments oring_zero {M} _.
Arguments oring_one {M} _.
Arguments oring_add {M} _ _ _.
Arguments oring_mul {M} _ _ _.
Arguments oring_lt {M} _ _ _.

Fixpoint oring_numeral {M} (O : oring_carrier M) (n : nat) : M :=
  match n with
  | 0 => oring_zero O
  | S k =>
      match k with
      | 0 => oring_one O
      | S _ => oring_add O (oring_numeral O k) (oring_one O)
      end
  end.

Lemma oring_numeral_zero : forall M (O : oring_carrier M),
  oring_numeral O 0 = oring_zero O.
Proof. reflexivity. Qed.

Lemma oring_numeral_one : forall M (O : oring_carrier M),
  oring_numeral O 1 = oring_one O.
Proof. reflexivity. Qed.

Lemma oring_numeral_succ_succ : forall M (O : oring_carrier M) n,
  oring_numeral O (S (S n)) =
  oring_add O (oring_numeral O (S n)) (oring_one O).
Proof. reflexivity. Qed.

Definition nat_oring_carrier : oring_carrier nat :=
  {| oring_zero := 0;
     oring_one := 1;
     oring_add := Nat.add;
     oring_mul := Nat.mul;
     oring_lt := lt |}.

Lemma nat_oring_numeral : forall n,
  oring_numeral nat_oring_carrier n = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct n as [|n]; [reflexivity|].
  change (Nat.add (oring_numeral nat_oring_carrier (S n)) 1 = S (S n)).
  rewrite IH. apply Nat.add_1_r.
Qed.

(** Arithmetic syntax aliases, kept as definitions rather than notation. *)
Definition arithmetic_semiterm X n := semiterm oring_language X n.
Definition arithmetic_term X := term oring_language X.
Definition arithmetic_semiformula X n := semiformula oring_language X n.
Definition arithmetic_formula X := formula oring_language X.
Definition arithmetic_semisentence n := semisentence oring_language n.
Definition arithmetic_sentence := sentence oring_language.
Definition arithmetic_semiproposition n := semiproposition oring_language n.
Definition arithmetic_proposition := proposition oring_language.

Definition semiterm_godel_number_term {L A X n}
    (Hz : semiterm_has_zero_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L) (E : encoding A)
    (a : A) : semiterm L X n :=
  semiterm_operator_apply
    (semiterm_godel_number (semiterm_godel_number_of_encoding Hz Ho Ha E) a)
    fin_zero.

Lemma semiterm_godel_number_term_eq : forall L A X n Hz Ho Ha
    (E : encoding A) (a : A),
  @semiterm_godel_number_term L A X n Hz Ho Ha E a =
  semiterm_operator_apply
    (semiterm_operator_numeral Hz Ho Ha (encode E a)) fin_zero.
Proof. reflexivity. Qed.

Lemma rew_semiterm_godel_number_term : forall L A X n Y m Hz Ho Ha
    (E : encoding A) (w : rew L X n Y m) (a : A),
  rew_apply w (semiterm_godel_number_term Hz Ho Ha E a) =
  semiterm_godel_number_term Hz Ho Ha E a.
Proof.
  intros. unfold semiterm_godel_number_term.
  rewrite rew_semiterm_operator_apply. f_equal.
  apply functional_extensionality. intro i. inversion i.
Qed.

Definition semiterm_one_term {L X n}
    (Ho : semiterm_has_one_operator L) : semiterm L X n :=
  semiterm_operator_apply (semiterm_one_operator Ho) fin_zero.

Definition semiterm_add_term {L X n}
    (Ha : semiterm_has_add_operator L)
    (t u : semiterm L X n) : semiterm L X n :=
  semiterm_operator_apply (semiterm_add_operator Ha) (fin_two t u).

Definition semiterm_add_one {L X n}
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L)
    (t : semiterm L X n) : semiterm L X n :=
  semiterm_add_term Ha t (semiterm_one_term Ho).

Lemma semiterm_val_fin_zero : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M),
  (fun i => semiterm_val Str b f (@fin_zero (semiterm L X n) i)) =
  @fin_zero M.
Proof.
  intros. apply functional_extensionality. intro i. inversion i.
Qed.

Lemma semiterm_val_fin_two : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (t u : semiterm L X n),
  (fun i => semiterm_val Str b f (fin_two t u i)) =
  fin_two (semiterm_val Str b f t) (semiterm_val Str b f u).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 1 i (fun j =>
    semiterm_val Str b f (fin_two t u j) =
    fin_two (semiterm_val Str b f t) (semiterm_val Str b f u) j)
    eq_refl _).
  intro j. refine (@Fin.caseS' 0 j (fun q =>
    semiterm_val Str b f (fin_two t u (Fin.FS q)) =
    fin_two (semiterm_val Str b f t) (semiterm_val Str b f u)
      (Fin.FS q)) eq_refl _).
  intros q; inversion q.
Qed.

Lemma semiterm_val_one_term : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (Ho : semiterm_has_one_operator L) one,
  structure_interprets_one Str Ho one ->
  semiterm_val Str b f (semiterm_one_term Ho) = one.
Proof.
  intros. unfold semiterm_one_term. rewrite semiterm_val_operator_apply.
  rewrite semiterm_val_fin_zero. apply structure_one_operator. exact H.
Qed.

Lemma semiterm_val_add_term : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (Ha : semiterm_has_add_operator L) (add : M -> M -> M)
    (t u : semiterm L X n),
  structure_interprets_add Str Ha add ->
  semiterm_val Str b f (semiterm_add_term Ha t u) =
  add (semiterm_val Str b f t) (semiterm_val Str b f u).
Proof.
  intros. unfold semiterm_add_term. rewrite semiterm_val_operator_apply.
  rewrite semiterm_val_fin_two. apply structure_add_operator. exact H.
Qed.

Lemma semiterm_val_add_one : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (Ho : semiterm_has_one_operator L) (Ha : semiterm_has_add_operator L)
    one (add : M -> M -> M) (t : semiterm L X n),
  structure_interprets_one Str Ho one ->
  structure_interprets_add Str Ha add ->
  semiterm_val Str b f (semiterm_add_one Ho Ha t) =
  add (semiterm_val Str b f t) one.
Proof.
  intros. unfold semiterm_add_one.
  rewrite (@semiterm_val_add_term L M X n Str b f Ha add t
    (semiterm_one_term Ho) H0).
  rewrite (@semiterm_val_one_term L M X n Str b f Ho one H).
  reflexivity.
Qed.

Record structure_interprets_oring (L : language) (M : Type)
    (Str : first_order_structure L M) (Lang : language_oring L)
    (O : oring_carrier M) : Prop := {
  structure_oring_zero :
    structure_interprets_zero Str
      (semiterm_zero_operator_of_language (language_oring_zero Lang))
      (oring_zero O);
  structure_oring_one :
    structure_interprets_one Str
      (semiterm_one_operator_of_language (language_oring_one Lang))
      (oring_one O);
  structure_oring_add :
    structure_interprets_add Str
      (semiterm_add_operator_of_language (language_oring_add Lang))
      (oring_add O);
  structure_oring_mul :
    structure_interprets_mul Str
      (semiterm_mul_operator_of_language (language_oring_mul Lang))
      (oring_mul O);
  structure_oring_eq :
    structure_interprets_eq Str
      (semiformula_eq_operator_of_language (language_oring_eq Lang));
  structure_oring_lt :
    structure_interprets_lt Str
      (semiformula_lt_operator_of_language (language_oring_lt Lang))
      (oring_lt O)
}.

Theorem semiterm_operator_val_numeral : forall L M
    (Str : first_order_structure L M)
    (Hz : semiterm_has_zero_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L) (O : oring_carrier M),
  structure_interprets_zero Str Hz (oring_zero O) ->
  structure_interprets_one Str Ho (oring_one O) ->
  structure_interprets_add Str Ha (oring_add O) ->
  forall n,
    semiterm_operator_val Str fin_zero
      (semiterm_operator_numeral Hz Ho Ha n) = oring_numeral O n.
Proof.
  intros L M Str Hz Ho Ha O Hzero Hone Hadd n.
  induction n as [|n IH].
  - apply structure_zero_operator. exact Hzero.
  - destruct n as [|n].
    + apply structure_one_operator. exact Hone.
    + rewrite semiterm_operator_numeral_succ_succ,
      semiterm_operator_val_comp.
      assert (Henv :
      (fun i => semiterm_operator_val Str fin_zero
        (fin_two (semiterm_operator_numeral Hz Ho Ha (S n))
          (semiterm_one_operator Ho) i)) =
      fin_two (oring_numeral O (S n)) (oring_one O)).
      { apply functional_extensionality. intro i.
        refine (@Fin.caseS' 1 i (fun j =>
        semiterm_operator_val Str fin_zero
          (fin_two (semiterm_operator_numeral Hz Ho Ha (S n))
            (semiterm_one_operator Ho) j) =
        fin_two (oring_numeral O (S n)) (oring_one O) j) _ _).
        - exact IH.
        - intro j. refine (@Fin.caseS' 0 j (fun q =>
          semiterm_operator_val Str fin_zero
            (fin_two (semiterm_operator_numeral Hz Ho Ha (S n))
              (semiterm_one_operator Ho) (Fin.FS q)) =
          fin_two (oring_numeral O (S n)) (oring_one O) (Fin.FS q)) _ _).
          + apply structure_one_operator. exact Hone.
          + intros q; inversion q. }
      rewrite Henv, (structure_add_operator Hadd). reflexivity.
Qed.

Definition semiformula_ball_lt_succ {L X n}
    (Hlt : semiformula_has_lt_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L)
    (t : semiterm L X n) (p : semiformula L X (S n)) :
    semiformula L X n :=
  semiformula_ball_lt Hlt (semiterm_add_one Ho Ha t) p.

Definition semiformula_bex_lt_succ {L X n}
    (Hlt : semiformula_has_lt_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L)
    (t : semiterm L X n) (p : semiformula L X (S n)) :
    semiformula L X n :=
  semiformula_bex_lt Hlt (semiterm_add_one Ho Ha t) p.

Lemma semiformula_eval_ball_lt_succ : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (Hlt : semiformula_has_lt_operator L)
    (Ho : semiterm_has_one_operator L) (Ha : semiterm_has_add_operator L)
    (lt : M -> M -> Prop) one (add : M -> M -> M)
    (t : semiterm L X n) (p : semiformula L X (S n)),
  structure_interprets_lt Str Hlt lt ->
  structure_interprets_one Str Ho one ->
  structure_interprets_add Str Ha add ->
  (semiformula_eval Str b f (semiformula_ball_lt_succ Hlt Ho Ha t p) <->
   forall x, lt x (add (semiterm_val Str b f t) one) ->
     semiformula_eval Str (fin_env_cons x b) f p).
Proof.
  intros. unfold semiformula_ball_lt_succ.
  rewrite semiformula_eval_ball_lt.
  setoid_rewrite (structure_relation_operator H).
  rewrite (@semiterm_val_add_one L M X n Str b f Ho Ha one add t H0 H1).
  reflexivity.
Qed.

Lemma semiformula_eval_bex_lt_succ : forall L M X n
    (Str : first_order_structure L M) (b : Fin.t n -> M) (f : X -> M)
    (Hlt : semiformula_has_lt_operator L)
    (Ho : semiterm_has_one_operator L) (Ha : semiterm_has_add_operator L)
    (lt : M -> M -> Prop) one (add : M -> M -> M)
    (t : semiterm L X n) (p : semiformula L X (S n)),
  structure_interprets_lt Str Hlt lt ->
  structure_interprets_one Str Ho one ->
  structure_interprets_add Str Ha add ->
  (semiformula_eval Str b f (semiformula_bex_lt_succ Hlt Ho Ha t p) <->
   exists x, lt x (add (semiterm_val Str b f t) one) /\
     semiformula_eval Str (fin_env_cons x b) f p).
Proof.
  intros. unfold semiformula_bex_lt_succ.
  rewrite semiformula_eval_bex_lt.
  setoid_rewrite (structure_relation_operator H).
  rewrite (@semiterm_val_add_one L M X n Str b f Ho Ha one add t H0 H1).
  reflexivity.
Qed.
