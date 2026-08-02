(**
  Finite formula folds and iterated simultaneous substitution.

  This ports the standard mathematical core of
  [Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Iteration.lean].
  The source specializes its substitution iteration to ordered-ring numerals.
  Here the distinguished terms form an arbitrary family [numeral], so every
  theorem also applies to other languages and term enumerations.

  The representation-independent fold homomorphisms are proved once and then
  reused for negation, shifting, and substitution.  A parallel raw-code layer
  connects the typed construction to the executable bootstrapping functions.
*)

From Stdlib Require Import Arith.PeanoNat Cantor Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic Typed.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import
  Basic Functions Typed Coding.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Typed finite folds *)

Fixpoint boot_formula_replicate {L X n}
    (p : semiformula L X n) (k : nat) : semiformula L X n :=
  match k with
  | 0 => p
  | S j => Semiformula_and p (boot_formula_replicate p j)
  end.

Lemma boot_formula_replicate_zero : forall L X n
    (p : semiformula L X n),
  boot_formula_replicate p 0 = p.
Proof. reflexivity. Qed.

Lemma boot_formula_replicate_succ : forall L X n
    (p : semiformula L X n) k,
  boot_formula_replicate p (S k) =
  Semiformula_and p (boot_formula_replicate p k).
Proof. reflexivity. Qed.

Fixpoint boot_formula_list_conj {L X n}
    (ps : list (semiformula L X n)) : semiformula L X n :=
  match ps with
  | [] => Semiformula_verum n
  | p :: qs => Semiformula_and p (boot_formula_list_conj qs)
  end.

Fixpoint boot_formula_list_disj {L X n}
    (ps : list (semiformula L X n)) : semiformula L X n :=
  match ps with
  | [] => Semiformula_falsum n
  | p :: qs => Semiformula_or p (boot_formula_list_disj qs)
  end.

Lemma boot_formula_list_conj_nil : forall L X n,
  @boot_formula_list_conj L X n [] = Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma boot_formula_list_conj_cons : forall L X n
    (p : semiformula L X n) ps,
  boot_formula_list_conj (p :: ps) =
  Semiformula_and p (boot_formula_list_conj ps).
Proof. reflexivity. Qed.

Lemma boot_formula_list_disj_nil : forall L X n,
  @boot_formula_list_disj L X n [] = Semiformula_falsum n.
Proof. reflexivity. Qed.

Lemma boot_formula_list_disj_cons : forall L X n
    (p : semiformula L X n) ps,
  boot_formula_list_disj (p :: ps) =
  Semiformula_or p (boot_formula_list_disj ps).
Proof. reflexivity. Qed.

Definition boot_formula_weight {L X n} (k : nat) : semiformula L X n :=
  boot_formula_list_conj (repeat (Semiformula_verum n) k).

Lemma boot_formula_weight_zero : forall L X n,
  @boot_formula_weight L X n 0 = Semiformula_verum n.
Proof. reflexivity. Qed.

Lemma boot_formula_weight_succ : forall L X n k,
  @boot_formula_weight L X n (S k) =
  Semiformula_and (Semiformula_verum n) (boot_formula_weight k).
Proof. reflexivity. Qed.

(** De Morgan duality is structural and needs no well-formedness premise. *)
Lemma boot_formula_neg_list_conj : forall L X n
    (ps : list (semiformula L X n)),
  semiformula_neg (boot_formula_list_conj ps) =
  boot_formula_list_disj (map semiformula_neg ps).
Proof.
  intros L X n ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

Lemma boot_formula_neg_list_disj : forall L X n
    (ps : list (semiformula L X n)),
  semiformula_neg (boot_formula_list_disj ps) =
  boot_formula_list_conj (map semiformula_neg ps).
Proof.
  intros L X n ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

(** One generic homomorphism theorem replaces separate shift and substitution
    inductions for both conjunction and disjunction. *)
Lemma boot_formula_rewrite_list_conj : forall L X n Y m
    (w : rew L X n Y m) (ps : list (semiformula L X n)),
  semiformula_rewrite w (boot_formula_list_conj ps) =
  boot_formula_list_conj (map (semiformula_rewrite w) ps).
Proof.
  intros L X n Y m w ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

Lemma boot_formula_rewrite_list_disj : forall L X n Y m
    (w : rew L X n Y m) (ps : list (semiformula L X n)),
  semiformula_rewrite w (boot_formula_list_disj ps) =
  boot_formula_list_disj (map (semiformula_rewrite w) ps).
Proof.
  intros L X n Y m w ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

Corollary boot_formula_shift_list_conj : forall L n
    (ps : list (semiproposition L n)),
  boot_typed_formula_shift (boot_formula_list_conj ps) =
  boot_formula_list_conj (map boot_typed_formula_shift ps).
Proof. intros. apply boot_formula_rewrite_list_conj. Qed.

Corollary boot_formula_shift_list_disj : forall L n
    (ps : list (semiproposition L n)),
  boot_typed_formula_shift (boot_formula_list_disj ps) =
  boot_formula_list_disj (map boot_typed_formula_shift ps).
Proof. intros. apply boot_formula_rewrite_list_disj. Qed.

Corollary boot_formula_subst_list_conj : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (ps : list (boot_typed_semiformula L n)),
  boot_typed_formula_subst v (boot_formula_list_conj ps) =
  boot_formula_list_conj (map (boot_typed_formula_subst v) ps).
Proof. intros. apply boot_formula_rewrite_list_conj. Qed.

Corollary boot_formula_subst_list_disj : forall L n m
    (v : boot_typed_semiterm_vec L n m)
    (ps : list (boot_typed_semiformula L n)),
  boot_typed_formula_subst v (boot_formula_list_disj ps) =
  boot_formula_list_disj (map (boot_typed_formula_subst v) ps).
Proof. intros. apply boot_formula_rewrite_list_disj. Qed.

(** * Raw conjunction and disjunction codes *)

Fixpoint boot_qq_conj_list (codes : list nat) : nat :=
  match codes with
  | [] => boot_qq_verum
  | p :: ps => boot_qq_and p (boot_qq_conj_list ps)
  end.

Fixpoint boot_qq_disj_list (codes : list nat) : nat :=
  match codes with
  | [] => boot_qq_falsum
  | p :: ps => boot_qq_or p (boot_qq_disj_list ps)
  end.

Lemma boot_qq_conj_list_nil : boot_qq_conj_list [] = boot_qq_verum.
Proof. reflexivity. Qed.

Lemma boot_qq_conj_list_cons : forall p ps,
  boot_qq_conj_list (p :: ps) = boot_qq_and p (boot_qq_conj_list ps).
Proof. reflexivity. Qed.

Lemma boot_qq_disj_list_nil : boot_qq_disj_list [] = boot_qq_falsum.
Proof. reflexivity. Qed.

Lemma boot_qq_disj_list_cons : forall p ps,
  boot_qq_disj_list (p :: ps) = boot_qq_or p (boot_qq_disj_list ps).
Proof. reflexivity. Qed.

Lemma boot_formula_list_conj_quote : forall L X n EL EX
    (ps : list (semiformula L X n)),
  semiformula_code EL EX (boot_formula_list_conj ps) =
  boot_qq_conj_list (map (semiformula_code EL EX) ps).
Proof.
  intros L X n EL EX ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

Lemma boot_formula_list_disj_quote : forall L X n EL EX
    (ps : list (semiformula L X n)),
  semiformula_code EL EX (boot_formula_list_disj ps) =
  boot_qq_disj_list (map (semiformula_code EL EX) ps).
Proof.
  intros L X n EL EX ps. induction ps as [|p ps IH]; simpl; now rewrite ?IH.
Qed.

Lemma boot_qq_conj_list_recognized : forall L n EL codes,
  Forall (@boot_is_semiformula L EL n) codes ->
  boot_is_semiformula EL n (boot_qq_conj_list codes).
Proof.
  intros L n EL codes H. induction H; simpl.
  - apply Boot_formula_verum.
  - now apply Boot_formula_and.
Qed.

Lemma boot_qq_disj_list_recognized : forall L n EL codes,
  Forall (@boot_is_semiformula L EL n) codes ->
  boot_is_semiformula EL n (boot_qq_disj_list codes).
Proof.
  intros L n EL codes H. induction H; simpl.
  - apply Boot_formula_falsum.
  - now apply Boot_formula_or.
Qed.

(** Exact inversion of the two raw Boolean constructors.  These lemmas are
    useful beyond iteration and isolate all representation-specific pairing
    arithmetic from the list proofs below. *)
Local Opaque Cantor.to_nat.

Lemma boot_is_semiformula_and_iff : forall L n EL p q,
  @boot_is_semiformula L EL n (boot_qq_and p q) <->
  boot_is_semiformula EL n p /\ boot_is_semiformula EL n q.
Proof.
  intros L n EL p q. split.
  - intro H.
    destruct (boot_is_semiformula_has_quote H) as [r Hcode].
    destruct r; simpl in Hcode.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Hbody. apply Cantor.to_nat_inj in Hbody.
      injection Hbody as Hleft Hright. split.
      * rewrite <- Hleft. apply semiformula_code_is_semiformula.
      * rewrite <- Hright. apply semiformula_code_is_semiformula.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_and in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
  - intros [Hp Hq]. now apply Boot_formula_and.
Qed.

Lemma boot_is_semiformula_or_iff : forall L n EL p q,
  @boot_is_semiformula L EL n (boot_qq_or p q) <->
  boot_is_semiformula EL n p /\ boot_is_semiformula EL n q.
Proof.
  intros L n EL p q. split.
  - intro H.
    destruct (boot_is_semiformula_has_quote H) as [r Hcode].
    destruct r; simpl in Hcode.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Hbody. apply Cantor.to_nat_inj in Hbody.
      injection Hbody as Hleft Hright. split.
      * rewrite <- Hleft. apply semiformula_code_is_semiformula.
      * rewrite <- Hright. apply semiformula_code_is_semiformula.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
    + unfold boot_qq_or in Hcode. apply Cantor.to_nat_inj in Hcode.
      injection Hcode as Htag _. discriminate Htag.
  - intros [Hp Hq]. now apply Boot_formula_or.
Qed.

Theorem boot_qq_conj_list_recognized_iff : forall L n EL codes,
  @boot_is_semiformula L EL n (boot_qq_conj_list codes) <->
  Forall (@boot_is_semiformula L EL n) codes.
Proof.
  intros L n EL codes. induction codes as [|p ps IH]; simpl.
  - split; intro; constructor.
  - rewrite boot_is_semiformula_and_iff, IH. split.
    + intros [Hp Hps]. now constructor.
    + intro H. inversion H; subst. now split.
Qed.

Theorem boot_qq_disj_list_recognized_iff : forall L n EL codes,
  @boot_is_semiformula L EL n (boot_qq_disj_list codes) <->
  Forall (@boot_is_semiformula L EL n) codes.
Proof.
  intros L n EL codes. induction codes as [|p ps IH]; simpl.
  - split; intro; constructor.
  - rewrite boot_is_semiformula_or_iff, IH. split.
    + intros [Hp Hps]. now constructor.
    + intro H. inversion H; subst. now split.
Qed.

(** Cantor pairing makes every nonempty conjunction code strictly larger
    than its tail, yielding the source length bound without model arithmetic. *)
Lemma boot_qq_conj_tail_lt : forall p q,
  q < boot_qq_and p q.
Proof.
  intros p q. unfold boot_qq_and.
  pose proof (Cantor.to_nat_non_decreasing p q) as Hinner.
  pose proof (Cantor.to_nat_non_decreasing 4 (Cantor.to_nat (p, q))) as Houter.
  lia.
Qed.

Lemma boot_qq_conj_list_length_le : forall codes,
  length codes <= boot_qq_conj_list codes.
Proof.
  intro codes. induction codes as [|p ps IH]; simpl.
  - lia.
  - pose proof (boot_qq_conj_tail_lt p (boot_qq_conj_list ps)). lia.
Qed.

Definition boot_qq_verums (k : nat) : nat :=
  boot_qq_conj_list (repeat boot_qq_verum k).

Lemma boot_qq_verums_zero : boot_qq_verums 0 = boot_qq_verum.
Proof. reflexivity. Qed.

Lemma boot_qq_verums_succ : forall k,
  boot_qq_verums (S k) = boot_qq_and boot_qq_verum (boot_qq_verums k).
Proof. reflexivity. Qed.

Lemma boot_qq_verums_bound : forall k, k <= boot_qq_verums k.
Proof.
  intro k. unfold boot_qq_verums.
  pose proof (boot_qq_conj_list_length_le
    (repeat boot_qq_verum k)) as H.
  now rewrite repeat_length in H.
Qed.

Lemma boot_qq_verums_recognized : forall L n EL k,
  @boot_is_semiformula L EL n (boot_qq_verums k).
Proof.
  intros L n EL k. apply boot_qq_conj_list_recognized.
  induction k as [|k IH]; simpl.
  - constructor.
  - constructor; [apply Boot_formula_verum|exact IH].
Qed.

Lemma boot_formula_weight_quote : forall L X n EL EX k,
  semiformula_code EL EX (@boot_formula_weight L X n k) =
  boot_qq_verums k.
Proof.
  intros. unfold boot_formula_weight, boot_qq_verums.
  rewrite boot_formula_list_conj_quote, map_repeat.
  reflexivity.
Qed.

(** * Iterated simultaneous substitution *)

Fixpoint boot_formula_subst_iteration {L n m}
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n))
    (k : nat) : list (boot_typed_semiformula L m) :=
  match k with
  | 0 => []
  | S j =>
      boot_typed_formula_subst (fin_coding_cons (numeral j) w) p ::
      boot_formula_subst_iteration numeral w p j
  end.

Lemma boot_formula_subst_iteration_zero : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)),
  boot_formula_subst_iteration numeral w p 0 = [].
Proof. reflexivity. Qed.

Lemma boot_formula_subst_iteration_succ : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_formula_subst_iteration numeral w p (S k) =
  boot_typed_formula_subst (fin_coding_cons (numeral k) w) p ::
    boot_formula_subst_iteration numeral w p k.
Proof. reflexivity. Qed.

Lemma boot_formula_subst_iteration_length : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  length (boot_formula_subst_iteration numeral w p k) = k.
Proof. intros. induction k; simpl; congruence. Qed.

Lemma boot_formula_subst_iteration_nth_error : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k i,
  i < k ->
  nth_error (boot_formula_subst_iteration numeral w p k) i =
  Some (boot_typed_formula_subst
    (fin_coding_cons (numeral (k - S i)) w) p).
Proof.
  intros L n m numeral w p k. induction k as [|k IH]; intros i Hi.
  - lia.
  - destruct i as [|i]; simpl.
    + replace (k - 0) with k by lia. reflexivity.
    + apply IH. lia.
Qed.

(** Pointwise composition with an adjoined vector is factored independently
    of formulas and is reused by both iteration naturality proofs. *)
Lemma boot_typed_subst_fin_coding_cons : forall L n m l
    (v : boot_typed_semiterm_vec L m l)
    (t : boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m),
  (fun i => boot_typed_subst v (fin_coding_cons t w i)) =
  fin_coding_cons (boot_typed_subst v t)
    (fun i => boot_typed_subst v (w i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    boot_typed_subst v (fin_coding_cons t w j) =
    fin_coding_cons (boot_typed_subst v t)
      (fun u => boot_typed_subst v (w u)) j) _ _); reflexivity.
Qed.

Lemma boot_typed_shift_fin_coding_cons : forall L n m
    (t : boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m),
  (fun i => boot_typed_shift (fin_coding_cons t w i)) =
  fin_coding_cons (boot_typed_shift t)
    (fun i => boot_typed_shift (w i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    boot_typed_shift (fin_coding_cons t w j) =
    fin_coding_cons (boot_typed_shift t)
      (fun u => boot_typed_shift (w u)) j) _ _); reflexivity.
Qed.

Lemma boot_formula_subst_iteration_neg : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  map boot_typed_formula_neg
    (boot_formula_subst_iteration numeral w p k) =
  boot_formula_subst_iteration numeral w (boot_typed_formula_neg p) k.
Proof.
  intros. induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite boot_typed_formula_subst_neg, IH. reflexivity.
Qed.

Lemma boot_formula_subst_iteration_shift : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  map boot_typed_formula_shift
    (boot_formula_subst_iteration numeral w p k) =
  boot_formula_subst_iteration
    (fun j => boot_typed_shift (numeral j))
    (fun i => boot_typed_shift (w i))
    (boot_typed_formula_shift p) k.
Proof.
  intros. induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite boot_typed_formula_shift_subst,
      boot_typed_shift_fin_coding_cons, IH. reflexivity.
Qed.

Lemma boot_formula_subst_iteration_subst : forall L n m l
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n))
    (v : boot_typed_semiterm_vec L m l) k,
  map (boot_typed_formula_subst v)
    (boot_formula_subst_iteration numeral w p k) =
  boot_formula_subst_iteration
    (fun j => boot_typed_subst v (numeral j))
    (fun i => boot_typed_subst v (w i)) p k.
Proof.
  intros. induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite boot_typed_formula_subst_subst,
      boot_typed_subst_fin_coding_cons, IH. reflexivity.
Qed.

Definition boot_formula_subst_iteration_conj {L n m}
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) (k : nat) :=
  boot_formula_list_conj (boot_formula_subst_iteration numeral w p k).

Definition boot_formula_subst_iteration_disj {L n m}
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) (k : nat) :=
  boot_formula_list_disj (boot_formula_subst_iteration numeral w p k).

(** This is the typed, language-generic form of the source's
    [disjSeqSubst]. *)
Definition boot_formula_disj_seq_subst := @boot_formula_subst_iteration_disj.

Lemma boot_formula_disj_seq_subst_zero : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)),
  boot_formula_disj_seq_subst numeral w p 0 = Semiformula_falsum m.
Proof. reflexivity. Qed.

Lemma boot_formula_disj_seq_subst_succ : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_formula_disj_seq_subst numeral w p (S k) =
  Semiformula_or
    (boot_typed_formula_subst (fin_coding_cons (numeral k) w) p)
    (boot_formula_disj_seq_subst numeral w p k).
Proof. reflexivity. Qed.

Theorem boot_formula_neg_conj_subst_iteration : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_typed_formula_neg
    (boot_formula_subst_iteration_conj numeral w p k) =
  boot_formula_subst_iteration_disj numeral w
    (boot_typed_formula_neg p) k.
Proof.
  intros. unfold boot_formula_subst_iteration_conj,
    boot_formula_subst_iteration_disj, boot_typed_formula_neg.
  rewrite boot_formula_neg_list_conj. f_equal.
  apply boot_formula_subst_iteration_neg.
Qed.

Theorem boot_formula_neg_disj_subst_iteration : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_typed_formula_neg
    (boot_formula_subst_iteration_disj numeral w p k) =
  boot_formula_subst_iteration_conj numeral w
    (boot_typed_formula_neg p) k.
Proof.
  intros. unfold boot_formula_subst_iteration_conj,
    boot_formula_subst_iteration_disj, boot_typed_formula_neg.
  rewrite boot_formula_neg_list_disj. f_equal.
  apply boot_formula_subst_iteration_neg.
Qed.

Theorem boot_formula_shift_conj_subst_iteration : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_typed_formula_shift
    (boot_formula_subst_iteration_conj numeral w p k) =
  boot_formula_subst_iteration_conj
    (fun j => boot_typed_shift (numeral j))
    (fun i => boot_typed_shift (w i))
    (boot_typed_formula_shift p) k.
Proof.
  intros. unfold boot_formula_subst_iteration_conj.
  rewrite boot_formula_shift_list_conj,
    boot_formula_subst_iteration_shift. reflexivity.
Qed.

Theorem boot_formula_shift_disj_subst_iteration : forall L n m
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_typed_formula_shift
    (boot_formula_subst_iteration_disj numeral w p k) =
  boot_formula_subst_iteration_disj
    (fun j => boot_typed_shift (numeral j))
    (fun i => boot_typed_shift (w i))
    (boot_typed_formula_shift p) k.
Proof.
  intros. unfold boot_formula_subst_iteration_disj.
  rewrite boot_formula_shift_list_disj,
    boot_formula_subst_iteration_shift. reflexivity.
Qed.

Theorem boot_formula_subst_conj_subst_iteration : forall L n m l
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n))
    (v : boot_typed_semiterm_vec L m l) k,
  boot_typed_formula_subst v
    (boot_formula_subst_iteration_conj numeral w p k) =
  boot_formula_subst_iteration_conj
    (fun j => boot_typed_subst v (numeral j))
    (fun i => boot_typed_subst v (w i)) p k.
Proof.
  intros. unfold boot_formula_subst_iteration_conj.
  rewrite boot_formula_subst_list_conj,
    boot_formula_subst_iteration_subst. reflexivity.
Qed.

Theorem boot_formula_subst_disj_subst_iteration : forall L n m l
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n))
    (v : boot_typed_semiterm_vec L m l) k,
  boot_typed_formula_subst v
    (boot_formula_subst_iteration_disj numeral w p k) =
  boot_formula_subst_iteration_disj
    (fun j => boot_typed_subst v (numeral j))
    (fun i => boot_typed_subst v (w i)) p k.
Proof.
  intros. unfold boot_formula_subst_iteration_disj.
  rewrite boot_formula_subst_list_disj,
    boot_formula_subst_iteration_subst. reflexivity.
Qed.

(** * Executable raw-code iteration *)

Fixpoint boot_formula_subst_iteration_codes {L n m}
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (pcode : nat) (k : nat) : list nat :=
  match k with
  | 0 => []
  | S j =>
      boot_formula_subst_code EL (fin_coding_cons (numeral j) w) pcode ::
      boot_formula_subst_iteration_codes EL numeral w pcode j
  end.

Lemma boot_formula_subst_iteration_codes_quote : forall L n m
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_formula_subst_iteration_codes EL numeral w
      (boot_typed_formula_quote EL p) k =
  map (boot_typed_formula_quote EL)
    (boot_formula_subst_iteration numeral w p k).
Proof.
  intros. unfold boot_typed_formula_quote.
  induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite boot_formula_subst_code_quote, IH. reflexivity.
Qed.

Definition boot_formula_disj_seq_subst_code {L n m}
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (pcode : nat) (k : nat) : nat :=
  boot_qq_disj_list
    (boot_formula_subst_iteration_codes EL numeral w pcode k).

Lemma boot_formula_disj_seq_subst_code_zero : forall L n m
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m) p,
  @boot_formula_disj_seq_subst_code L n m EL numeral w p 0 =
  boot_qq_falsum.
Proof. reflexivity. Qed.

Lemma boot_formula_disj_seq_subst_code_succ : forall L n m
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m) p k,
  @boot_formula_disj_seq_subst_code L n m EL numeral w p (S k) =
  boot_qq_or
    (boot_formula_subst_code EL (fin_coding_cons (numeral k) w) p)
    (boot_formula_disj_seq_subst_code EL numeral w p k).
Proof. reflexivity. Qed.

Lemma boot_formula_disj_seq_subst_code_quote : forall L n m
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m)
    (p : boot_typed_semiformula L (S n)) k,
  boot_formula_disj_seq_subst_code EL numeral w
      (boot_typed_formula_quote EL p) k =
  boot_typed_formula_quote EL
    (boot_formula_disj_seq_subst numeral w p k).
Proof.
  intros. unfold boot_formula_disj_seq_subst_code,
    boot_formula_disj_seq_subst, boot_formula_subst_iteration_disj.
  rewrite boot_formula_subst_iteration_codes_quote.
  change (boot_qq_disj_list
      (map (semiformula_code EL boot_nat_encoding)
        (boot_formula_subst_iteration numeral w p k)) =
    semiformula_code EL boot_nat_encoding
      (boot_formula_list_disj
        (boot_formula_subst_iteration numeral w p k))).
  symmetry. apply boot_formula_list_disj_quote.
Qed.

Theorem boot_formula_disj_seq_subst_code_recognized : forall L n m
    (EL : language_encodable L)
    (numeral : nat -> boot_typed_semiterm L m)
    (w : boot_typed_semiterm_vec L n m) pcode k,
  @boot_is_semiformula L EL (S n) pcode ->
  boot_is_semiformula EL m
    (boot_formula_disj_seq_subst_code EL numeral w pcode k).
Proof.
  intros L n m EL numeral w pcode k Hp.
  unfold boot_formula_disj_seq_subst_code.
  apply boot_qq_disj_list_recognized.
  induction k as [|k IH]; simpl.
  - constructor.
  - constructor.
    + now apply boot_formula_subst_code_preserves.
    + exact IH.
Qed.
