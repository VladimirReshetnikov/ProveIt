(** Monadic second-order formulas in negation-normal form. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive second_order_semiformula (L : language) (P X : Type) :
    nat -> nat -> Type :=
| SOFormula_rel : forall N n k,
    language_rel L k -> (Fin.t k -> semiterm L X n) ->
    second_order_semiformula L P X N n
| SOFormula_nrel : forall N n k,
    language_rel L k -> (Fin.t k -> semiterm L X n) ->
    second_order_semiformula L P X N n
| SOFormula_bpred : forall N n,
    Fin.t N -> semiterm L X n -> second_order_semiformula L P X N n
| SOFormula_nbpred : forall N n,
    Fin.t N -> semiterm L X n -> second_order_semiformula L P X N n
| SOFormula_fpred : forall N n,
    P -> semiterm L X n -> second_order_semiformula L P X N n
| SOFormula_nfpred : forall N n,
    P -> semiterm L X n -> second_order_semiformula L P X N n
| SOFormula_verum : forall N n, second_order_semiformula L P X N n
| SOFormula_falsum : forall N n, second_order_semiformula L P X N n
| SOFormula_and : forall N n,
    second_order_semiformula L P X N n ->
    second_order_semiformula L P X N n ->
    second_order_semiformula L P X N n
| SOFormula_or : forall N n,
    second_order_semiformula L P X N n ->
    second_order_semiformula L P X N n ->
    second_order_semiformula L P X N n
| SOFormula_all0 : forall N n,
    second_order_semiformula L P X N (S n) ->
    second_order_semiformula L P X N n
| SOFormula_exs0 : forall N n,
    second_order_semiformula L P X N (S n) ->
    second_order_semiformula L P X N n
| SOFormula_all1 : forall N n,
    second_order_semiformula L P X (S N) n ->
    second_order_semiformula L P X N n
| SOFormula_exs1 : forall N n,
    second_order_semiformula L P X (S N) n ->
    second_order_semiformula L P X N n.

Arguments SOFormula_rel {L P X N n k} _ _.
Arguments SOFormula_nrel {L P X N n k} _ _.
Arguments SOFormula_bpred {L P X N n} _ _.
Arguments SOFormula_nbpred {L P X N n} _ _.
Arguments SOFormula_fpred {L P X N n} _ _.
Arguments SOFormula_nfpred {L P X N n} _ _.
Arguments SOFormula_verum {L P X N n}.
Arguments SOFormula_falsum {L P X N n}.
Arguments SOFormula_and {L P X N n} _ _.
Arguments SOFormula_or {L P X N n} _ _.
Arguments SOFormula_all0 {L P X N n} _.
Arguments SOFormula_exs0 {L P X N n} _.
Arguments SOFormula_all1 {L P X N n} _.
Arguments SOFormula_exs1 {L P X N n} _.

Definition second_order_formula L P X :=
  second_order_semiformula L P X 0 0.

Definition second_order_semisentence L N n :=
  second_order_semiformula L Empty_set Empty_set N n.

Definition second_order_sentence L :=
  second_order_semiformula L Empty_set Empty_set 0 0.

Definition second_order_semiproposition L N n :=
  second_order_semiformula L nat nat N n.

Definition second_order_proposition L :=
  second_order_semiformula L nat nat 0 0.

Fixpoint second_order_neg {L P X N n}
    (p : second_order_semiformula L P X N n) :
    second_order_semiformula L P X N n :=
  match p with
  | SOFormula_rel r v => SOFormula_nrel r v
  | SOFormula_nrel r v => SOFormula_rel r v
  | SOFormula_bpred A t => SOFormula_nbpred A t
  | SOFormula_nbpred A t => SOFormula_bpred A t
  | SOFormula_fpred A t => SOFormula_nfpred A t
  | SOFormula_nfpred A t => SOFormula_fpred A t
  | SOFormula_verum => SOFormula_falsum
  | SOFormula_falsum => SOFormula_verum
  | SOFormula_and q r => SOFormula_or (second_order_neg q)
      (second_order_neg r)
  | SOFormula_or q r => SOFormula_and (second_order_neg q)
      (second_order_neg r)
  | SOFormula_all0 q => SOFormula_exs0 (second_order_neg q)
  | SOFormula_exs0 q => SOFormula_all0 (second_order_neg q)
  | SOFormula_all1 q => SOFormula_exs1 (second_order_neg q)
  | SOFormula_exs1 q => SOFormula_all1 (second_order_neg q)
  end.

Definition second_order_imp {L P X N n}
    (p q : second_order_semiformula L P X N n) :=
  SOFormula_or (second_order_neg p) q.

Definition second_order_iff {L P X N n}
    (p q : second_order_semiformula L P X N n) :=
  SOFormula_and (second_order_imp p q) (second_order_imp q p).

Lemma second_order_neg_rel : forall L P X N n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  @second_order_neg L P X N n (SOFormula_rel r v) = SOFormula_nrel r v.
Proof. reflexivity. Qed.

Lemma second_order_neg_nrel : forall L P X N n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  @second_order_neg L P X N n (SOFormula_nrel r v) = SOFormula_rel r v.
Proof. reflexivity. Qed.

Lemma second_order_neg_bpred : forall L P X N n
    (A : Fin.t N) (t : semiterm L X n),
  @second_order_neg L P X N n (@SOFormula_bpred L P X N n A t) =
  @SOFormula_nbpred L P X N n A t.
Proof. reflexivity. Qed.

Lemma second_order_neg_nbpred : forall L P X N n
    (A : Fin.t N) (t : semiterm L X n),
  @second_order_neg L P X N n (@SOFormula_nbpred L P X N n A t) =
  @SOFormula_bpred L P X N n A t.
Proof. reflexivity. Qed.

Lemma second_order_neg_fpred : forall L P X N n
    (A : P) (t : semiterm L X n),
  @second_order_neg L P X N n (@SOFormula_fpred L P X N n A t) =
  @SOFormula_nfpred L P X N n A t.
Proof. reflexivity. Qed.

Lemma second_order_neg_nfpred : forall L P X N n
    (A : P) (t : semiterm L X n),
  @second_order_neg L P X N n (@SOFormula_nfpred L P X N n A t) =
  @SOFormula_fpred L P X N n A t.
Proof. reflexivity. Qed.

Lemma second_order_neg_verum : forall L P X N n,
  @second_order_neg L P X N n SOFormula_verum = SOFormula_falsum.
Proof. reflexivity. Qed.

Lemma second_order_neg_falsum : forall L P X N n,
  @second_order_neg L P X N n SOFormula_falsum = SOFormula_verum.
Proof. reflexivity. Qed.

Lemma second_order_neg_and : forall L P X N n
    (p q : second_order_semiformula L P X N n),
  second_order_neg (SOFormula_and p q) =
  SOFormula_or (second_order_neg p) (second_order_neg q).
Proof. reflexivity. Qed.

Lemma second_order_neg_or : forall L P X N n
    (p q : second_order_semiformula L P X N n),
  second_order_neg (SOFormula_or p q) =
  SOFormula_and (second_order_neg p) (second_order_neg q).
Proof. reflexivity. Qed.

Lemma second_order_neg_all0 : forall L P X N n
    (p : second_order_semiformula L P X N (S n)),
  second_order_neg (SOFormula_all0 p) =
  SOFormula_exs0 (second_order_neg p).
Proof. reflexivity. Qed.

Lemma second_order_neg_exs0 : forall L P X N n
    (p : second_order_semiformula L P X N (S n)),
  second_order_neg (SOFormula_exs0 p) =
  SOFormula_all0 (second_order_neg p).
Proof. reflexivity. Qed.

Lemma second_order_neg_all1 : forall L P X N n
    (p : second_order_semiformula L P X (S N) n),
  second_order_neg (SOFormula_all1 p) =
  SOFormula_exs1 (second_order_neg p).
Proof. reflexivity. Qed.

Lemma second_order_neg_exs1 : forall L P X N n
    (p : second_order_semiformula L P X (S N) n),
  second_order_neg (SOFormula_exs1 p) =
  SOFormula_all1 (second_order_neg p).
Proof. reflexivity. Qed.

Theorem second_order_neg_involutive : forall L P X N n
    (p : second_order_semiformula L P X N n),
  second_order_neg (second_order_neg p) = p.
Proof.
  intros L P X N n p. induction p; simpl; congruence.
Qed.

Corollary second_order_neg_injective : forall L P X N n
    (p q : second_order_semiformula L P X N n),
  second_order_neg p = second_order_neg q -> p = q.
Proof.
  intros L P X N n p q H.
  rewrite <- (second_order_neg_involutive p),
    <- (second_order_neg_involutive q).
  now rewrite H.
Qed.

(** Constructor projections avoid any use of dependent-pair injectivity. *)

Definition second_order_and_left {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N n) :=
  match p with
  | SOFormula_and q _ => Some q
  | _ => None
  end.

Definition second_order_and_right {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N n) :=
  match p with
  | SOFormula_and _ q => Some q
  | _ => None
  end.

Definition second_order_or_left {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N n) :=
  match p with
  | SOFormula_or q _ => Some q
  | _ => None
  end.

Definition second_order_or_right {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N n) :=
  match p with
  | SOFormula_or _ q => Some q
  | _ => None
  end.

Definition second_order_all0_body {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N (S n)) :=
  match p with
  | SOFormula_all0 q => Some q
  | _ => None
  end.

Definition second_order_exs0_body {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X N (S n)) :=
  match p with
  | SOFormula_exs0 q => Some q
  | _ => None
  end.

Definition second_order_all1_body {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X (S N) n) :=
  match p with
  | SOFormula_all1 q => Some q
  | _ => None
  end.

Definition second_order_exs1_body {L P X N n}
    (p : second_order_semiformula L P X N n) :
    option (second_order_semiformula L P X (S N) n) :=
  match p with
  | SOFormula_exs1 q => Some q
  | _ => None
  end.

Lemma second_order_and_injective : forall L P X N n
    (p q r s : second_order_semiformula L P X N n),
  SOFormula_and p q = SOFormula_and r s <-> p = r /\ q = s.
Proof.
  split.
  - intro H. split.
    + pose proof (f_equal second_order_and_left H) as E.
      simpl in E. now injection E.
    + pose proof (f_equal second_order_and_right H) as E.
      simpl in E. now injection E.
  - intros [-> ->]. reflexivity.
Qed.

Lemma second_order_or_injective : forall L P X N n
    (p q r s : second_order_semiformula L P X N n),
  SOFormula_or p q = SOFormula_or r s <-> p = r /\ q = s.
Proof.
  split.
  - intro H. split.
    + pose proof (f_equal second_order_or_left H) as E.
      simpl in E. now injection E.
    + pose proof (f_equal second_order_or_right H) as E.
      simpl in E. now injection E.
  - intros [-> ->]. reflexivity.
Qed.

Lemma second_order_all0_injective : forall L P X N n
    (p q : second_order_semiformula L P X N (S n)),
  SOFormula_all0 p = SOFormula_all0 q <-> p = q.
Proof.
  split.
  - intro H. pose proof (f_equal second_order_all0_body H) as E.
    simpl in E. now injection E.
  - now intros ->.
Qed.

Lemma second_order_exs0_injective : forall L P X N n
    (p q : second_order_semiformula L P X N (S n)),
  SOFormula_exs0 p = SOFormula_exs0 q <-> p = q.
Proof.
  split.
  - intro H. pose proof (f_equal second_order_exs0_body H) as E.
    simpl in E. now injection E.
  - now intros ->.
Qed.

Lemma second_order_all1_injective : forall L P X N n
    (p q : second_order_semiformula L P X (S N) n),
  SOFormula_all1 p = SOFormula_all1 q <-> p = q.
Proof.
  split.
  - intro H. pose proof (f_equal second_order_all1_body H) as E.
    simpl in E. now injection E.
  - now intros ->.
Qed.

Lemma second_order_exs1_injective : forall L P X N n
    (p q : second_order_semiformula L P X (S N) n),
  SOFormula_exs1 p = SOFormula_exs1 q <-> p = q.
Proof.
  split.
  - intro H. pose proof (f_equal second_order_exs1_body H) as E.
    simpl in E. now injection E.
  - now intros ->.
Qed.

Fixpoint second_order_complexity {L P X N n}
    (p : second_order_semiformula L P X N n) : nat :=
  match p with
  | SOFormula_rel _ _ | SOFormula_nrel _ _
  | SOFormula_bpred _ _ | SOFormula_nbpred _ _
  | SOFormula_fpred _ _ | SOFormula_nfpred _ _
  | SOFormula_verum | SOFormula_falsum => 0
  | SOFormula_and q r | SOFormula_or q r =>
      Nat.max (second_order_complexity q) (second_order_complexity r) + 1
  | SOFormula_all0 q | SOFormula_exs0 q
  | SOFormula_all1 q | SOFormula_exs1 q =>
      second_order_complexity q + 1
  end.

Lemma second_order_complexity_rel : forall L P X N n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  second_order_complexity (@SOFormula_rel L P X N n k r v) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_nrel : forall L P X N n k
    (r : language_rel L k) (v : Fin.t k -> semiterm L X n),
  second_order_complexity (@SOFormula_nrel L P X N n k r v) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_bpred : forall L P X N n
    (A : Fin.t N) (t : semiterm L X n),
  second_order_complexity (@SOFormula_bpred L P X N n A t) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_nbpred : forall L P X N n
    (A : Fin.t N) (t : semiterm L X n),
  second_order_complexity (@SOFormula_nbpred L P X N n A t) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_fpred : forall L P X N n
    (A : P) (t : semiterm L X n),
  second_order_complexity (@SOFormula_fpred L P X N n A t) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_nfpred : forall L P X N n
    (A : P) (t : semiterm L X n),
  second_order_complexity (@SOFormula_nfpred L P X N n A t) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_verum : forall L P X N n,
  second_order_complexity
    (@SOFormula_verum L P X N n) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_falsum : forall L P X N n,
  second_order_complexity
    (@SOFormula_falsum L P X N n) = 0.
Proof. reflexivity. Qed.

Lemma second_order_complexity_and : forall L P X N n
    (p q : second_order_semiformula L P X N n),
  second_order_complexity (SOFormula_and p q) =
  Nat.max (second_order_complexity p) (second_order_complexity q) + 1.
Proof. reflexivity. Qed.

Lemma second_order_complexity_or : forall L P X N n
    (p q : second_order_semiformula L P X N n),
  second_order_complexity (SOFormula_or p q) =
  Nat.max (second_order_complexity p) (second_order_complexity q) + 1.
Proof. reflexivity. Qed.

Lemma second_order_complexity_all0 : forall L P X N n
    (p : second_order_semiformula L P X N (S n)),
  second_order_complexity (SOFormula_all0 p) =
  second_order_complexity p + 1.
Proof. reflexivity. Qed.

Lemma second_order_complexity_exs0 : forall L P X N n
    (p : second_order_semiformula L P X N (S n)),
  second_order_complexity (SOFormula_exs0 p) =
  second_order_complexity p + 1.
Proof. reflexivity. Qed.

Lemma second_order_complexity_all1 : forall L P X N n
    (p : second_order_semiformula L P X (S N) n),
  second_order_complexity (SOFormula_all1 p) =
  second_order_complexity p + 1.
Proof. reflexivity. Qed.

Lemma second_order_complexity_exs1 : forall L P X N n
    (p : second_order_semiformula L P X (S N) n),
  second_order_complexity (SOFormula_exs1 p) =
  second_order_complexity p + 1.
Proof. reflexivity. Qed.

Theorem second_order_complexity_neg : forall L P X N n
    (p : second_order_semiformula L P X N n),
  second_order_complexity (second_order_neg p) =
  second_order_complexity p.
Proof.
  intros L P X N n p. induction p; simpl; congruence.
Qed.
