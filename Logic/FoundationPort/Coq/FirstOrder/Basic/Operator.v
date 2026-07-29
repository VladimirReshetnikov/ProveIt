(**
  First-order term and formula operators.

  This ports the foundational operator algebra from
  [Foundation/FirstOrder/Basic/Operator.lean].  Operators are closed templates
  whose bound variables are their argument slots.  Their action is therefore
  simultaneous instantiation by [rew_emb_substs].  Keeping this description
  explicit makes composition, rewrite naturality, occurrence, and positivity
  consequences of the generic rewrite algebra, without decidable equality or
  equality of proof-carrying rewrite records.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Small finite argument vectors *)

Definition fin_zero {A : Type} (i : Fin.t 0) : A := match i with end.

Definition fin_one {A : Type} (x : A) (i : Fin.t 1) : A :=
  @Fin.caseS' 0 i (fun _ => A) x (fun z => match z with end).

Definition fin_two {A : Type} (x y : A) (i : Fin.t 2) : A :=
  @Fin.caseS' 1 i (fun _ => A) x
    (fun j => @Fin.caseS' 0 j (fun _ => A) y (fun z => match z with end)).

Lemma fin_two_first : forall A (x y : A), fin_two x y Fin.F1 = x.
Proof. reflexivity. Qed.

Lemma fin_one_only : forall A (x : A), fin_one x Fin.F1 = x.
Proof. reflexivity. Qed.

Lemma fin_two_second : forall A (x y : A),
  fin_two x y (Fin.FS Fin.F1) = y.
Proof. reflexivity. Qed.

Lemma fin_one_eta : forall A (v : Fin.t 1 -> A),
  v = fin_one (v Fin.F1).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 0 i (fun j => v j = fin_one (v Fin.F1) j)
    eq_refl _).
  intros q; inversion q.
Qed.

Lemma fin_two_eta : forall A (v : Fin.t 2 -> A),
  v = fin_two (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 1 i
    (fun j => v j = fin_two (v Fin.F1) (v (Fin.FS Fin.F1)) j)
    eq_refl _).
  intro j. refine (@Fin.caseS' 0 j
    (fun q => v (Fin.FS q) =
      fin_two (v Fin.F1) (v (Fin.FS Fin.F1)) (Fin.FS q))
    eq_refl _).
  intros q; inversion q.
Qed.

Fixpoint fin_to_list {A : Type} (n : nat) :
    (Fin.t n -> A) -> list A :=
  match n as k return (Fin.t k -> A) -> list A with
  | 0 => fun _ => []
  | S k => fun v => v Fin.F1 :: @fin_to_list A k (fun i => v (Fin.FS i))
  end.

(** * Semiterm operators *)

Record semiterm_operator (L : language) (arity : nat) : Type := {
  semiterm_operator_term : closed_semiterm L arity
}.

Arguments semiterm_operator_term {L arity} _.

Definition semiterm_const_operator L := semiterm_operator L 0.

Definition semiterm_operator_fn {L k}
    (f : language_func L k) : semiterm_operator L k :=
  {| semiterm_operator_term := Semiterm_func f (fun i => Semiterm_bvar i) |}.

Definition semiterm_operator_apply {L k X n}
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X n) :
    semiterm L X n :=
  rew_apply (rew_emb_substs v) (semiterm_operator_term o).

Definition semiterm_operator_const_apply {L X n}
    (c : semiterm_const_operator L) : semiterm L X n :=
  semiterm_operator_apply c fin_zero.

Lemma semiterm_operator_ext : forall L k (o p : semiterm_operator L k),
  semiterm_operator_term o = semiterm_operator_term p -> o = p.
Proof. intros L k [o] [p]; simpl; now intros ->. Qed.

Lemma semiterm_operator_fn_apply : forall L k X n
    (f : language_func L k) (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_fn f) v =
  Semiterm_func f v.
Proof.
  intros. unfold semiterm_operator_apply, semiterm_operator_fn; simpl.
  reflexivity.
Qed.

(** Every rewrite acts homomorphically on every operator.  The statement is
    more general than the source's specialized syntactic rewrite wrappers: the
    free-variable types and both bound arities may all change. *)
Lemma rew_semiterm_operator_apply : forall L X n Y m k
    (w : rew L X n Y m) (o : semiterm_operator L k)
    (v : Fin.t k -> semiterm L X n),
  rew_apply w (semiterm_operator_apply o v) =
  semiterm_operator_apply o (fun i => rew_apply w (v i)).
Proof.
  intros L X n Y m k w o v.
  unfold semiterm_operator_apply.
  change
    (rew_apply (rew_comp w (rew_emb_substs v))
      (semiterm_operator_term o) =
     rew_apply (rew_emb_substs (fun i => rew_apply w (v i)))
      (semiterm_operator_term o)).
  apply rew_comp_emb_substs.
Qed.

Definition semiterm_operator_comp {L k l}
    (o : semiterm_operator L k)
    (w : Fin.t k -> semiterm_operator L l) : semiterm_operator L l :=
  {| semiterm_operator_term :=
       semiterm_operator_apply o (fun i => semiterm_operator_term (w i)) |}.

Lemma semiterm_operator_comp_apply : forall L k l X n
    (o : semiterm_operator L k) (w : Fin.t k -> semiterm_operator L l)
    (v : Fin.t l -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_comp o w) v =
  semiterm_operator_apply o
    (fun i => semiterm_operator_apply (w i) v).
Proof.
  intros. unfold semiterm_operator_comp; simpl.
  apply rew_semiterm_operator_apply.
Qed.

Definition semiterm_operator_bvar {L n}
    (i : Fin.t n) : semiterm_operator L n :=
  {| semiterm_operator_term := Semiterm_bvar i |}.

Lemma semiterm_operator_bvar_apply : forall L k X n (i : Fin.t k)
    (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_bvar (L := L) i) v = v i.
Proof. reflexivity. Qed.

Lemma semiterm_operator_comp_bvar_left : forall L k l (i : Fin.t k)
    (w : Fin.t k -> semiterm_operator L l),
  semiterm_operator_comp (semiterm_operator_bvar (L := L) i) w = w i.
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply semiterm_operator_bvar_apply.
Qed.

Lemma semiterm_operator_comp_bvar_right : forall L k
    (o : semiterm_operator L k),
  semiterm_operator_comp o
    (fun i => semiterm_operator_bvar (L := L) i) = o.
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply rew_emb_substs_variables_empty.
Qed.

Lemma semiterm_operator_comp_assoc : forall L k l r
    (o : semiterm_operator L k)
    (w : Fin.t k -> semiterm_operator L l)
    (u : Fin.t l -> semiterm_operator L r),
  semiterm_operator_comp (semiterm_operator_comp o w) u =
  semiterm_operator_comp o (fun i => semiterm_operator_comp (w i) u).
Proof.
  intros. apply semiterm_operator_ext. simpl.
  apply semiterm_operator_comp_apply.
Qed.

(** Exact occurrence and positivity laws.  Predicate-valued occurrence avoids
    the source's finite-set and decidable-equality side conditions. *)
Lemma semiterm_operator_apply_bound_occurs : forall L k X n
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X n) j,
  semiterm_bound_occurs j (semiterm_operator_apply o v) <->
  exists i : Fin.t k,
    semiterm_bound_occurs i (semiterm_operator_term o) /\
    semiterm_bound_occurs j (v i).
Proof.
  intros. apply rew_emb_substs_bound_occurs.
Qed.

Lemma semiterm_operator_apply_positive : forall L k X n
    (o : semiterm_operator L k) (v : Fin.t k -> semiterm L X (S n)),
  semiterm_positive (semiterm_operator_apply o v) <->
  forall i, semiterm_bound_occurs i (semiterm_operator_term o) ->
    semiterm_positive (v i).
Proof.
  intros. apply rew_emb_substs_positive.
Qed.

Lemma semiterm_const_operator_positive : forall L X n
    (c : semiterm_const_operator L),
  semiterm_positive (@semiterm_operator_const_apply L X (S n) c).
Proof.
  intros. apply (proj2 (semiterm_operator_apply_positive c fin_zero)).
  intros i. inversion i.
Qed.

Fixpoint semiterm_operator_foldr {L k}
    (f : semiterm_operator L 2) (z : semiterm_operator L k)
    (os : list (semiterm_operator L k)) : semiterm_operator L k :=
  match os with
  | [] => z
  | o :: tail =>
      semiterm_operator_comp f
        (fin_two (semiterm_operator_foldr f z tail) o)
  end.

Lemma semiterm_operator_foldr_nil : forall L k
    (f : semiterm_operator L 2) (z : semiterm_operator L k),
  semiterm_operator_foldr f z [] = z.
Proof. reflexivity. Qed.

Lemma semiterm_operator_foldr_cons_apply : forall L k X n
    (f : semiterm_operator L 2) (z o : semiterm_operator L k)
    (os : list (semiterm_operator L k))
    (v : Fin.t k -> semiterm L X n),
  semiterm_operator_apply (semiterm_operator_foldr f z (o :: os)) v =
  semiterm_operator_apply f
    (fin_two
      (semiterm_operator_apply (semiterm_operator_foldr f z os) v)
      (semiterm_operator_apply o v)).
Proof.
  intros. simpl. rewrite semiterm_operator_comp_apply.
  f_equal. apply functional_extensionality. intro i.
  refine (@Fin.caseS' 1 i (fun j =>
    semiterm_operator_apply (fin_two (semiterm_operator_foldr f z os) o j) v =
    fin_two
      (semiterm_operator_apply (semiterm_operator_foldr f z os) v)
      (semiterm_operator_apply o v) j) _ _).
  - reflexivity.
  - intro j. refine (@Fin.caseS' 0 j (fun q => _) _ _).
    + reflexivity.
    + intros q; inversion q.
Qed.

(** The positive-arity branch follows the source exactly: the fold starts at
    the first variable and traverses the remaining variables in finite-index
    order. *)
Definition semiterm_operator_iterr {L}
    (f : semiterm_operator L 2) (z : semiterm_const_operator L)
    (n : nat) : semiterm_operator L n :=
  match n as k return semiterm_operator L k with
  | 0 => z
  | S k => semiterm_operator_foldr f
      (semiterm_operator_bvar (L := L) Fin.F1)
      (@fin_to_list (semiterm_operator L (S k)) k
        (fun i => semiterm_operator_bvar (L := L) (Fin.FS i)))
  end.

Lemma semiterm_operator_iterr_zero : forall L
    (f : semiterm_operator L 2) (z : semiterm_const_operator L),
  semiterm_operator_iterr f z 0 = z.
Proof. reflexivity. Qed.

Lemma semiterm_operator_iterr_succ : forall L
    (f : semiterm_operator L 2) (z : semiterm_const_operator L) n,
  semiterm_operator_iterr f z (S n) =
  semiterm_operator_foldr f
    (semiterm_operator_bvar (L := L) Fin.F1)
    (@fin_to_list (semiterm_operator L (S n)) n
      (fun i => semiterm_operator_bvar (L := L) (Fin.FS i))).
Proof. reflexivity. Qed.

(** * Named term-operator capabilities *)

Record semiterm_has_zero_operator (L : language) : Type :=
  { semiterm_zero_operator : semiterm_const_operator L }.
Record semiterm_has_one_operator (L : language) : Type :=
  { semiterm_one_operator : semiterm_const_operator L }.
Record semiterm_has_add_operator (L : language) : Type :=
  { semiterm_add_operator : semiterm_operator L 2 }.
Record semiterm_has_mul_operator (L : language) : Type :=
  { semiterm_mul_operator : semiterm_operator L 2 }.
Record semiterm_has_exp_operator (L : language) : Type :=
  { semiterm_exp_operator : semiterm_operator L 1 }.
Record semiterm_has_sub_operator (L : language) : Type :=
  { semiterm_sub_operator : semiterm_operator L 2 }.
Record semiterm_has_div_operator (L : language) : Type :=
  { semiterm_div_operator : semiterm_operator L 2 }.
Record semiterm_has_star_operator (L : language) : Type :=
  { semiterm_star_operator : semiterm_const_operator L }.

Record semiterm_godel_number_operator (L : language) (A : Type) : Type :=
  { semiterm_godel_number : A -> semiterm_const_operator L }.

Definition semiterm_zero_operator_of_language {L}
    (H : language_has_zero L) : semiterm_has_zero_operator L :=
  {| semiterm_zero_operator := semiterm_operator_fn (language_zero H) |}.

Definition semiterm_one_operator_of_language {L}
    (H : language_has_one L) : semiterm_has_one_operator L :=
  {| semiterm_one_operator := semiterm_operator_fn (language_one H) |}.

Definition semiterm_add_operator_of_language {L}
    (H : language_has_add L) : semiterm_has_add_operator L :=
  {| semiterm_add_operator := semiterm_operator_fn (language_add_symbol H) |}.

Definition semiterm_mul_operator_of_language {L}
    (H : language_has_mul L) : semiterm_has_mul_operator L :=
  {| semiterm_mul_operator := semiterm_operator_fn (language_mul_symbol H) |}.

Definition semiterm_exp_operator_of_language {L}
    (H : language_has_exp L) : semiterm_has_exp_operator L :=
  {| semiterm_exp_operator := semiterm_operator_fn (language_exp_symbol H) |}.

Definition semiterm_star_operator_of_language {L}
    (H : language_has_star L) : semiterm_has_star_operator L :=
  {| semiterm_star_operator := semiterm_operator_fn (language_star H) |}.

Lemma semiterm_add_operator_positive : forall L X n
    (H : language_has_add L) (t u : semiterm L X (S n)),
  semiterm_positive
    (semiterm_operator_apply
      (semiterm_add_operator
        (semiterm_add_operator_of_language H)) (fin_two t u)) <->
  semiterm_positive t /\ semiterm_positive u.
Proof.
  intros. change
    (semiterm_positive
      (semiterm_operator_apply
        (semiterm_operator_fn (language_add_symbol H)) (fin_two t u)) <->
     semiterm_positive t /\ semiterm_positive u).
  rewrite semiterm_operator_fn_apply, semiterm_positive_func.
  split.
  - intro Hp. split; [apply (Hp Fin.F1) | apply (Hp (Fin.FS Fin.F1))].
  - intros [Ht Hu] i.
    refine (@Fin.caseS' 1 i (fun j => semiterm_positive (fin_two t u j))
      Ht _).
    intro j. refine (@Fin.caseS' 0 j
      (fun q => semiterm_positive (fin_two t u (Fin.FS q))) Hu _).
    intros q; inversion q.
Qed.

Lemma semiterm_mul_operator_positive : forall L X n
    (H : language_has_mul L) (t u : semiterm L X (S n)),
  semiterm_positive
    (semiterm_operator_apply
      (semiterm_mul_operator
        (semiterm_mul_operator_of_language H)) (fin_two t u)) <->
  semiterm_positive t /\ semiterm_positive u.
Proof.
  intros. change
    (semiterm_positive
      (semiterm_operator_apply
        (semiterm_operator_fn (language_mul_symbol H)) (fin_two t u)) <->
     semiterm_positive t /\ semiterm_positive u).
  rewrite semiterm_operator_fn_apply, semiterm_positive_func.
  split.
  - intro Hp. split; [apply (Hp Fin.F1) | apply (Hp (Fin.FS Fin.F1))].
  - intros [Ht Hu] i.
    refine (@Fin.caseS' 1 i (fun j => semiterm_positive (fin_two t u j))
      Ht _).
    intro j. refine (@Fin.caseS' 0 j
      (fun q => semiterm_positive (fin_two t u (Fin.FS q))) Hu _).
    intros q; inversion q.
Qed.

Lemma semiterm_exp_operator_positive : forall L X n
    (H : language_has_exp L) (t : semiterm L X (S n)),
  semiterm_positive
    (semiterm_operator_apply
      (semiterm_exp_operator
        (semiterm_exp_operator_of_language H)) (fin_one t)) <->
  semiterm_positive t.
Proof.
  intros. change
    (semiterm_positive
      (semiterm_operator_apply
        (semiterm_operator_fn (language_exp_symbol H)) (fin_one t)) <->
     semiterm_positive t).
  rewrite semiterm_operator_fn_apply, semiterm_positive_func.
  split.
  - intro Hp. apply (Hp Fin.F1).
  - intros Ht i. refine (@Fin.caseS' 0 i
      (fun j => semiterm_positive (fin_one t j)) Ht _).
    intros q; inversion q.
Qed.

(** Numerals use only abstract zero, one, and addition operators; they do not
    require those operators to be primitive language symbols. *)
Definition semiterm_operator_numeral {L}
    (Hz : semiterm_has_zero_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L) (n : nat) :
    semiterm_const_operator L :=
  match n with
  | 0 => semiterm_zero_operator Hz
  | S k => semiterm_operator_foldr (semiterm_add_operator Ha)
      (semiterm_one_operator Ho) (repeat (semiterm_one_operator Ho) k)
  end.

Lemma semiterm_operator_numeral_zero : forall L Hz Ho Ha,
  @semiterm_operator_numeral L Hz Ho Ha 0 = semiterm_zero_operator Hz.
Proof. reflexivity. Qed.

Lemma semiterm_operator_numeral_one : forall L Hz Ho Ha,
  @semiterm_operator_numeral L Hz Ho Ha 1 = semiterm_one_operator Ho.
Proof. reflexivity. Qed.

Lemma semiterm_operator_numeral_succ_nonzero : forall L Hz Ho Ha n,
  n <> 0 ->
  @semiterm_operator_numeral L Hz Ho Ha (S n) =
  semiterm_operator_comp (semiterm_add_operator Ha)
    (fin_two (@semiterm_operator_numeral L Hz Ho Ha n)
      (semiterm_one_operator Ho)).
Proof.
  intros L Hz Ho Ha [|n] H; [now exfalso; apply H | reflexivity].
Qed.

Lemma semiterm_operator_numeral_succ_succ : forall L Hz Ho Ha n,
  @semiterm_operator_numeral L Hz Ho Ha (S (S n)) =
  semiterm_operator_comp (semiterm_add_operator Ha)
    (fin_two (@semiterm_operator_numeral L Hz Ho Ha (S n))
      (semiterm_one_operator Ho)).
Proof.
  intros. apply semiterm_operator_numeral_succ_nonzero. discriminate.
Qed.

Definition semiterm_godel_number_of_encoding {L A}
    (Hz : semiterm_has_zero_operator L)
    (Ho : semiterm_has_one_operator L)
    (Ha : semiterm_has_add_operator L) (E : encoding A) :
    semiterm_godel_number_operator L A :=
  {| semiterm_godel_number :=
       fun a => semiterm_operator_numeral Hz Ho Ha (encode E a) |}.

(** Unary natural powers, again parameterized by abstract one and
    multiplication operators. *)
Definition semiterm_operator_npow {L}
    (Ho : semiterm_has_one_operator L)
    (Hm : semiterm_has_mul_operator L) (n : nat) : semiterm_operator L 1 :=
  semiterm_operator_foldr (semiterm_mul_operator Hm)
    (semiterm_operator_comp (semiterm_one_operator Ho) fin_zero)
    (repeat (semiterm_operator_bvar (L := L) Fin.F1) n).

Lemma semiterm_operator_npow_zero : forall L Ho Hm,
  @semiterm_operator_npow L Ho Hm 0 =
  semiterm_operator_comp (semiterm_one_operator Ho) fin_zero.
Proof. reflexivity. Qed.

Lemma semiterm_operator_npow_succ : forall L Ho Hm n,
  @semiterm_operator_npow L Ho Hm (S n) =
  semiterm_operator_comp (semiterm_mul_operator Hm)
    (fin_two (@semiterm_operator_npow L Ho Hm n)
      (semiterm_operator_bvar (L := L) Fin.F1)).
Proof. reflexivity. Qed.

Lemma semiterm_operator_npow_positive : forall L X n
    (Ho : semiterm_has_one_operator L) (Hm : language_has_mul L)
    (t : semiterm L X (S n)) k,
  semiterm_positive
    (semiterm_operator_apply
      (@semiterm_operator_npow L Ho
        (semiterm_mul_operator_of_language Hm) k) (fin_one t)) <->
  k = 0 \/ semiterm_positive t.
Proof.
  intros L X n Ho Hm t k; induction k as [|k IH].
  - rewrite semiterm_operator_npow_zero, semiterm_operator_comp_apply.
    split; [intro; now left | intros _].
    replace
      (fun i : Fin.t 0 =>
        semiterm_operator_apply (fin_zero i) (fin_one t))
      with (@fin_zero (semiterm L X (S n))).
    + apply semiterm_const_operator_positive.
    + apply functional_extensionality. intro i; inversion i.
  - rewrite semiterm_operator_npow_succ, semiterm_operator_comp_apply.
    replace
      (fun i : Fin.t 2 =>
        semiterm_operator_apply
          (fin_two
            (@semiterm_operator_npow L Ho
              (semiterm_mul_operator_of_language Hm) k)
            (semiterm_operator_bvar (L := L) Fin.F1) i)
          (fin_one t))
      with
      (fin_two
        (semiterm_operator_apply
          (@semiterm_operator_npow L Ho
            (semiterm_mul_operator_of_language Hm) k) (fin_one t)) t).
    + rewrite semiterm_mul_operator_positive, IH. split.
      * intros [_ Hp]. now right.
      * intros [H | Hp]; [discriminate H |].
        split; [now right | exact Hp].
    + apply functional_extensionality. intro i.
      refine (@Fin.caseS' 1 i (fun j => _) eq_refl _).
      intro j. refine (@Fin.caseS' 0 j (fun q => _) _ _).
      * symmetry. apply semiterm_operator_bvar_apply.
      * intros q; inversion q.
Qed.

(** Exact complexities for the canonical primitive arithmetic operators. *)
Lemma fin_max_two : forall (v : Fin.t 2 -> nat),
  @fin_max 2 v = Nat.max (v Fin.F1) (v (Fin.FS Fin.F1)).
Proof.
  intro v. simpl. now rewrite Nat.max_0_r.
Qed.

Lemma semiterm_zero_operator_complexity : forall L X n
    (H : language_has_zero L),
  semiterm_complexity
    (@semiterm_operator_const_apply L X n
      (semiterm_zero_operator
        (semiterm_zero_operator_of_language H))) = 1.
Proof. reflexivity. Qed.

Lemma semiterm_one_operator_complexity : forall L X n
    (H : language_has_one L),
  semiterm_complexity
    (@semiterm_operator_const_apply L X n
      (semiterm_one_operator
        (semiterm_one_operator_of_language H))) = 1.
Proof. reflexivity. Qed.

Lemma semiterm_add_operator_complexity : forall L X n
    (H : language_has_add L) (t u : semiterm L X n),
  semiterm_complexity
    (semiterm_operator_apply
      (semiterm_add_operator
        (semiterm_add_operator_of_language H)) (fin_two t u)) =
  S (Nat.max (semiterm_complexity t) (semiterm_complexity u)).
Proof.
  intros. change
    (semiterm_complexity
      (semiterm_operator_apply
        (semiterm_operator_fn (language_add_symbol H)) (fin_two t u)) =
     S (Nat.max (semiterm_complexity t) (semiterm_complexity u))).
  rewrite semiterm_operator_fn_apply, semiterm_complexity_func.
  now rewrite fin_max_two.
Qed.

Lemma semiterm_mul_operator_complexity : forall L X n
    (H : language_has_mul L) (t u : semiterm L X n),
  semiterm_complexity
    (semiterm_operator_apply
      (semiterm_mul_operator
        (semiterm_mul_operator_of_language H)) (fin_two t u)) =
  S (Nat.max (semiterm_complexity t) (semiterm_complexity u)).
Proof.
  intros. change
    (semiterm_complexity
      (semiterm_operator_apply
        (semiterm_operator_fn (language_mul_symbol H)) (fin_two t u)) =
     S (Nat.max (semiterm_complexity t) (semiterm_complexity u))).
  rewrite semiterm_operator_fn_apply, semiterm_complexity_func.
  now rewrite fin_max_two.
Qed.

(** * Semiformula operators *)

Record semiformula_operator (L : language) (arity : nat) : Type := {
  semiformula_operator_sentence : semisentence L arity
}.

Arguments semiformula_operator_sentence {L arity} _.

Definition semiformula_const_operator L := semiformula_operator L 0.

Definition semiformula_operator_apply {L k X n}
    (o : semiformula_operator L k) (v : Fin.t k -> semiterm L X n) :
    semiformula L X n :=
  semiformula_rewrite (rew_emb_substs v) (semiformula_operator_sentence o).

Definition semiformula_operator_const_apply {L X n}
    (c : semiformula_const_operator L) : semiformula L X n :=
  semiformula_operator_apply c fin_zero.

Lemma semiformula_operator_ext : forall L k (o p : semiformula_operator L k),
  semiformula_operator_sentence o = semiformula_operator_sentence p -> o = p.
Proof. intros L k [o] [p]; simpl; now intros ->. Qed.

Lemma rew_semiformula_operator_apply : forall L X n Y m k
    (w : rew L X n Y m) (o : semiformula_operator L k)
    (v : Fin.t k -> semiterm L X n),
  semiformula_rewrite w (semiformula_operator_apply o v) =
  semiformula_operator_apply o (fun i => rew_apply w (v i)).
Proof.
  intros. unfold semiformula_operator_apply.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext.
  apply rew_comp_emb_substs.
Qed.

Definition semiformula_operator_comp {L k l}
    (o : semiformula_operator L k)
    (w : Fin.t k -> semiterm_operator L l) : semiformula_operator L l :=
  {| semiformula_operator_sentence :=
       semiformula_operator_apply o
         (fun i => semiterm_operator_term (w i)) |}.

Lemma semiformula_operator_comp_apply : forall L k l X n
    (o : semiformula_operator L k) (w : Fin.t k -> semiterm_operator L l)
    (v : Fin.t l -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_comp o w) v =
  semiformula_operator_apply o
    (fun i => semiterm_operator_apply (w i) v).
Proof.
  intros. unfold semiformula_operator_comp; simpl.
  apply rew_semiformula_operator_apply.
Qed.

Lemma semiformula_operator_comp_bvar_right : forall L k
    (o : semiformula_operator L k),
  semiformula_operator_comp o
    (fun i => semiterm_operator_bvar (L := L) i) = o.
Proof.
  intros. apply semiformula_operator_ext. simpl.
  transitivity
    (semiformula_rewrite (@rew_id L Empty_set k)
      (semiformula_operator_sentence o)).
  - apply semiformula_rewrite_ext.
    apply rew_emb_substs_variables_empty.
  - apply semiformula_rewrite_id.
Qed.

Lemma semiformula_operator_comp_assoc : forall L k l r
    (o : semiformula_operator L k)
    (w : Fin.t k -> semiterm_operator L l)
    (u : Fin.t l -> semiterm_operator L r),
  semiformula_operator_comp (semiformula_operator_comp o w) u =
  semiformula_operator_comp o (fun i => semiterm_operator_comp (w i) u).
Proof.
  intros. apply semiformula_operator_ext. simpl.
  apply semiformula_operator_comp_apply.
Qed.

Definition semiformula_operator_and {L k}
    (o p : semiformula_operator L k) : semiformula_operator L k :=
  {| semiformula_operator_sentence :=
       Semiformula_and (semiformula_operator_sentence o)
         (semiformula_operator_sentence p) |}.

Definition semiformula_operator_or {L k}
    (o p : semiformula_operator L k) : semiformula_operator L k :=
  {| semiformula_operator_sentence :=
       Semiformula_or (semiformula_operator_sentence o)
         (semiformula_operator_sentence p) |}.

Lemma semiformula_operator_and_apply : forall L k X n
    (o p : semiformula_operator L k) (v : Fin.t k -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_and o p) v =
  Semiformula_and (semiformula_operator_apply o v)
    (semiformula_operator_apply p v).
Proof. reflexivity. Qed.

Lemma semiformula_operator_or_apply : forall L k X n
    (o p : semiformula_operator L k) (v : Fin.t k -> semiterm L X n),
  semiformula_operator_apply (semiformula_operator_or o p) v =
  Semiformula_or (semiformula_operator_apply o v)
    (semiformula_operator_apply p v).
Proof. reflexivity. Qed.

(** * Named relation-operator capabilities *)

Record semiformula_has_eq_operator (L : language) : Type :=
  { semiformula_eq_operator : semiformula_operator L 2 }.
Record semiformula_has_lt_operator (L : language) : Type :=
  { semiformula_lt_operator : semiformula_operator L 2 }.
Record semiformula_has_le_operator (L : language) : Type :=
  { semiformula_le_operator : semiformula_operator L 2 }.
Record semiformula_has_mem_operator (L : language) : Type :=
  { semiformula_mem_operator : semiformula_operator L 2 }.

Definition semiformula_eq_operator_of_language {L}
    (H : language_has_eq L) : semiformula_has_eq_operator L :=
  {| semiformula_eq_operator :=
       {| semiformula_operator_sentence :=
            Semiformula_rel (language_eq H) (fun i => Semiterm_bvar i) |} |}.

Definition semiformula_lt_operator_of_language {L}
    (H : language_has_lt L) : semiformula_has_lt_operator L :=
  {| semiformula_lt_operator :=
       {| semiformula_operator_sentence :=
            Semiformula_rel (language_lt H) (fun i => Semiterm_bvar i) |} |}.

Definition semiformula_mem_operator_of_language {L}
    (H : language_has_mem L) : semiformula_has_mem_operator L :=
  {| semiformula_mem_operator :=
       {| semiformula_operator_sentence :=
            Semiformula_rel (language_mem H) (fun i => Semiterm_bvar i) |} |}.

Definition semiformula_le_operator_of_eq_lt {L}
    (Heq : semiformula_has_eq_operator L)
    (Hlt : semiformula_has_lt_operator L) : semiformula_has_le_operator L :=
  {| semiformula_le_operator :=
       semiformula_operator_or (semiformula_eq_operator Heq)
         (semiformula_lt_operator Hlt) |}.

Definition semiformula_le_operator_of_language {L}
    (Heq : language_has_eq L) (Hlt : language_has_lt L) :
    semiformula_has_le_operator L :=
  semiformula_le_operator_of_eq_lt
    (semiformula_eq_operator_of_language Heq)
    (semiformula_lt_operator_of_language Hlt).

Lemma semiformula_eq_operator_apply : forall L X n
    (H : language_has_eq L) (t u : semiterm L X n),
  semiformula_operator_apply
    (semiformula_eq_operator (semiformula_eq_operator_of_language H))
    (fin_two t u) =
  Semiformula_rel (language_eq H) (fin_two t u).
Proof. reflexivity. Qed.

Lemma semiformula_lt_operator_apply : forall L X n
    (H : language_has_lt L) (t u : semiterm L X n),
  semiformula_operator_apply
    (semiformula_lt_operator (semiformula_lt_operator_of_language H))
    (fin_two t u) =
  Semiformula_rel (language_lt H) (fin_two t u).
Proof. reflexivity. Qed.

Lemma semiformula_mem_operator_apply : forall L X n
    (H : language_has_mem L) (t u : semiterm L X n),
  semiformula_operator_apply
    (semiformula_mem_operator (semiformula_mem_operator_of_language H))
    (fin_two t u) =
  Semiformula_rel (language_mem H) (fin_two t u).
Proof. reflexivity. Qed.

Lemma semiformula_le_operator_apply : forall L X n
    (Heq : language_has_eq L) (Hlt : language_has_lt L)
    (t u : semiterm L X n),
  semiformula_operator_apply
    (semiformula_le_operator
      (semiformula_le_operator_of_language Heq Hlt)) (fin_two t u) =
  Semiformula_or
    (Semiformula_rel (language_eq Heq) (fin_two t u))
    (Semiformula_rel (language_lt Hlt) (fin_two t u)).
Proof. reflexivity. Qed.

(** * Rewrite preimages of binary atoms *)

Definition semiformula_outer_relation_arity {L X n}
    (p : semiformula L X n) : option nat :=
  match p with
  | @Semiformula_rel _ _ _ k _ _ => Some k
  | _ => None
  end.

Lemma semiformula_rel_arity_injective : forall L X n k l
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n)
    (s : language_rel L l) (w : Fin.t l -> semiterm L X n),
  Semiformula_rel r v = Semiformula_rel s w -> k = l.
Proof.
  intros L X n k l r v s w H.
  pose proof (f_equal semiformula_outer_relation_arity H) as Ha.
  simpl in Ha. now injection Ha.
Qed.

(** This single constructive theorem strictly generalizes the source's three
    equality/LT/membership lemmas.  It works for every binary relation symbol,
    every rewrite, and needs no decidable equality on symbols. *)
Lemma semiformula_rewrite_binary_relation_preimage : forall
    L X n Y m (w : rew L X n Y m) (p : semiformula L X n)
    (r : language_rel L 2) (t u : semiterm L Y m),
  semiformula_rewrite w p = Semiformula_rel r (fin_two t u) <->
  exists t' u' : semiterm L X n,
    rew_apply w t' = t /\ rew_apply w u' = u /\
    p = Semiformula_rel r (fin_two t' u').
Proof.
  intros L X n Y m w p r t u. split.
  - intro H. destruct p as
      [n0 | n0 | n0 k s v | n0 k s v |
       n0 p q | n0 p q | n0 p | n0 p];
      simpl in H; try discriminate H.
    destruct k as [|k].
    + pose proof (semiformula_rel_arity_injective H) as Hk.
      discriminate Hk.
    + destruct k as [|k].
      * pose proof (semiformula_rel_arity_injective H) as Hk.
        discriminate Hk.
      * destruct k as [|k].
        -- destruct (semiformula_rel_injective_same_arity H) as [Hs Hv].
           exists (v Fin.F1), (v (Fin.FS Fin.F1)).
           split.
           ++ exact (f_equal (fun a => a Fin.F1) Hv).
           ++ split.
              ** exact (f_equal (fun a => a (Fin.FS Fin.F1)) Hv).
              ** subst s. f_equal. apply fin_two_eta.
        -- pose proof (semiformula_rel_arity_injective H) as Hk.
           discriminate Hk.
  - intros [t' [u' [Ht [Hu ->]]]]. simpl.
    f_equal. apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i
      (fun j => rew_apply w (fin_two t' u' j) = fin_two t u j)
      Ht _).
    intro j. refine (@Fin.caseS' 0 j
      (fun q => rew_apply w (fin_two t' u' (Fin.FS q)) =
        fin_two t u (Fin.FS q)) Hu _).
    intros q; inversion q.
Qed.

Lemma semiformula_rewrite_eq_operator_preimage : forall
    L X n Y m (w : rew L X n Y m) (p : semiformula L X n)
    (H : language_has_eq L) (t u : semiterm L Y m),
  semiformula_rewrite w p =
    semiformula_operator_apply
      (semiformula_eq_operator (semiformula_eq_operator_of_language H))
      (fin_two t u) <->
  exists t' u' : semiterm L X n,
    rew_apply w t' = t /\ rew_apply w u' = u /\
    p = semiformula_operator_apply
      (semiformula_eq_operator (semiformula_eq_operator_of_language H))
      (fin_two t' u').
Proof.
  intros. rewrite !semiformula_eq_operator_apply.
  apply semiformula_rewrite_binary_relation_preimage.
Qed.

Lemma semiformula_rewrite_lt_operator_preimage : forall
    L X n Y m (w : rew L X n Y m) (p : semiformula L X n)
    (H : language_has_lt L) (t u : semiterm L Y m),
  semiformula_rewrite w p =
    semiformula_operator_apply
      (semiformula_lt_operator (semiformula_lt_operator_of_language H))
      (fin_two t u) <->
  exists t' u' : semiterm L X n,
    rew_apply w t' = t /\ rew_apply w u' = u /\
    p = semiformula_operator_apply
      (semiformula_lt_operator (semiformula_lt_operator_of_language H))
      (fin_two t' u').
Proof.
  intros. rewrite !semiformula_lt_operator_apply.
  apply semiformula_rewrite_binary_relation_preimage.
Qed.

Lemma semiformula_rewrite_mem_operator_preimage : forall
    L X n Y m (w : rew L X n Y m) (p : semiformula L X n)
    (H : language_has_mem L) (t u : semiterm L Y m),
  semiformula_rewrite w p =
    semiformula_operator_apply
      (semiformula_mem_operator (semiformula_mem_operator_of_language H))
      (fin_two t u) <->
  exists t' u' : semiterm L X n,
    rew_apply w t' = t /\ rew_apply w u' = u /\
    p = semiformula_operator_apply
      (semiformula_mem_operator (semiformula_mem_operator_of_language H))
      (fin_two t' u').
Proof.
  intros. rewrite !semiformula_mem_operator_apply.
  apply semiformula_rewrite_binary_relation_preimage.
Qed.

(** A single arity-two constructor theorem supplies equality, order, and
    membership injectivity, avoiding three copies of the same finite-vector
    argument. *)
Lemma semiformula_binary_relation_injective : forall L X n
    (r : language_rel L 2) (t1 u1 t2 u2 : semiterm L X n),
  Semiformula_rel r (fin_two t1 u1) =
  Semiformula_rel r (fin_two t2 u2) <-> t1 = t2 /\ u1 = u2.
Proof.
  intros. split.
  - intro H.
    pose proof (proj2 (semiformula_rel_injective_same_arity H)) as Hv.
    split.
    + exact (f_equal (fun v => v Fin.F1) Hv).
    + exact (f_equal (fun v => v (Fin.FS Fin.F1)) Hv).
  - now intros [-> ->].
Qed.

Lemma semiformula_eq_operator_injective : forall L X n
    (H : language_has_eq L) (t1 u1 t2 u2 : semiterm L X n),
  semiformula_operator_apply
      (semiformula_eq_operator (semiformula_eq_operator_of_language H))
      (fin_two t1 u1) =
    semiformula_operator_apply
      (semiformula_eq_operator (semiformula_eq_operator_of_language H))
      (fin_two t2 u2) <-> t1 = t2 /\ u1 = u2.
Proof.
  intros. rewrite !semiformula_eq_operator_apply.
  apply semiformula_binary_relation_injective.
Qed.

Lemma semiformula_lt_operator_injective : forall L X n
    (H : language_has_lt L) (t1 u1 t2 u2 : semiterm L X n),
  semiformula_operator_apply
      (semiformula_lt_operator (semiformula_lt_operator_of_language H))
      (fin_two t1 u1) =
    semiformula_operator_apply
      (semiformula_lt_operator (semiformula_lt_operator_of_language H))
      (fin_two t2 u2) <-> t1 = t2 /\ u1 = u2.
Proof.
  intros. rewrite !semiformula_lt_operator_apply.
  apply semiformula_binary_relation_injective.
Qed.

Lemma semiformula_mem_operator_injective : forall L X n
    (H : language_has_mem L) (t1 u1 t2 u2 : semiterm L X n),
  semiformula_operator_apply
      (semiformula_mem_operator (semiformula_mem_operator_of_language H))
      (fin_two t1 u1) =
    semiformula_operator_apply
      (semiformula_mem_operator (semiformula_mem_operator_of_language H))
      (fin_two t2 u2) <-> t1 = t2 /\ u1 = u2.
Proof.
  intros. rewrite !semiformula_mem_operator_apply.
  apply semiformula_binary_relation_injective.
Qed.

Lemma semiformula_le_operator_injective : forall L X n
    (Heq : language_has_eq L) (Hlt : language_has_lt L)
    (t1 u1 t2 u2 : semiterm L X n),
  semiformula_operator_apply
      (semiformula_le_operator
        (semiformula_le_operator_of_language Heq Hlt)) (fin_two t1 u1) =
    semiformula_operator_apply
      (semiformula_le_operator
        (semiformula_le_operator_of_language Heq Hlt)) (fin_two t2 u2) <->
  t1 = t2 /\ u1 = u2.
Proof.
  intros. rewrite !semiformula_le_operator_apply.
  rewrite semiformula_or_injective.
  split.
  - intros [He _]. now apply semiformula_binary_relation_injective in He.
  - intro H. split; now apply semiformula_binary_relation_injective.
Qed.

Lemma semiformula_eq_operator_open : forall L X n
    (H : language_has_eq L) (t u : semiterm L X n),
  semiformula_open
    (semiformula_operator_apply
      (semiformula_eq_operator (semiformula_eq_operator_of_language H))
      (fin_two t u)).
Proof. intros; rewrite semiformula_eq_operator_apply; reflexivity. Qed.

Lemma semiformula_lt_operator_open : forall L X n
    (H : language_has_lt L) (t u : semiterm L X n),
  semiformula_open
    (semiformula_operator_apply
      (semiformula_lt_operator (semiformula_lt_operator_of_language H))
      (fin_two t u)).
Proof. intros; rewrite semiformula_lt_operator_apply; reflexivity. Qed.

Lemma semiformula_mem_operator_open : forall L X n
    (H : language_has_mem L) (t u : semiterm L X n),
  semiformula_open
    (semiformula_operator_apply
      (semiformula_mem_operator (semiformula_mem_operator_of_language H))
      (fin_two t u)).
Proof. intros; rewrite semiformula_mem_operator_apply; reflexivity. Qed.

Lemma semiformula_le_operator_open : forall L X n
    (Heq : language_has_eq L) (Hlt : language_has_lt L)
    (t u : semiterm L X n),
  semiformula_open
    (semiformula_operator_apply
      (semiformula_le_operator
        (semiformula_le_operator_of_language Heq Hlt)) (fin_two t u)).
Proof. intros; rewrite semiformula_le_operator_apply; reflexivity. Qed.

(** Bounded quantifiers retain an abstract relation-operator premise, so
    clients may use definable relations rather than primitive symbols. *)
Definition semiformula_ball_lt {L X n}
    (H : semiformula_has_lt_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_all
    (semiformula_operator_apply (semiformula_lt_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.

Definition semiformula_bex_lt {L X n}
    (H : semiformula_has_lt_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_exists
    (semiformula_operator_apply (semiformula_lt_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.

Definition semiformula_ball_le {L X n}
    (H : semiformula_has_le_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_all
    (semiformula_operator_apply (semiformula_le_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.

Definition semiformula_bex_le {L X n}
    (H : semiformula_has_le_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_exists
    (semiformula_operator_apply (semiformula_le_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.

Definition semiformula_ball_mem {L X n}
    (H : semiformula_has_mem_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_all
    (semiformula_operator_apply (semiformula_mem_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.

Definition semiformula_bex_mem {L X n}
    (H : semiformula_has_mem_operator L) (t : semiterm L X n)
    (p : semiformula L X (S n)) : semiformula L X n :=
  semiformula_bounded_exists
    (semiformula_operator_apply (semiformula_mem_operator H)
      (fin_two (Semiterm_bvar Fin.F1) (rew_apply rew_bshift t)))
    p.
