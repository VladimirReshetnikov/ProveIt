(** Iterated provability and the least inconsistent iteration.

    This is the representation-independent core of Foundation's
    [ProvabilityAbstraction/Height.lean].  The source is phrased for quoted
    first-order sentences; its proofs use only two theorem predicates, a
    provability endomorphism, reflection, and extended-natural minimization.
    We consequently retain the more general formula-atom interface of
    [ProvabilityAbstraction]. *)

From Stdlib Require Import Arith.PeanoNat Lia.
From FoundationModal Require Import
  Syntax LogicInfrastructure GenericModalLogicSymbol.
From Foundation.Vorspiel Require Import ENat.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pa_iter {A L0 L} (B : pa_provability L0 L)
    (n : nat) (p : formula A) : formula A :=
  generic_modal_iter (pa_box B) n p.

Definition pa_dia_iter {A L0 L} (B : pa_provability L0 L)
    (n : nat) (p : formula A) : formula A :=
  generic_modal_iter (pa_dia B) n p.

Lemma pa_iter_zero : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) p,
  pa_iter B 0 p = p.
Proof. reflexivity. Qed.

Lemma pa_iter_succ : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) n p,
  pa_iter B (S n) p = pa_box B (pa_iter B n p).
Proof. reflexivity. Qed.

Lemma pa_iter_add : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) n m p,
  pa_iter B n (pa_iter B m p) = pa_iter B (n + m) p.
Proof.
  intros A L0 L B n m p. unfold pa_iter.
  apply generic_modal_iter_add.
Qed.

(** Foundation uses an involutive, negation-normal-form sentence negation,
    so its corresponding statement is syntactic equality.  With ordinary
    formulas, where [Neg p] is [p -> Bottom], the invariant is instead a
    theorem-level biconditional. *)
Lemma pa_neg_iterated_prov : forall (A : Type)
    (L0 L : modal_logic_set A)
    (Hclass0 : classical_logic L0) (Hweak : logic_subset L0 L)
    (B : pa_provability L0 L),
  pa_ext B -> forall n p,
  L0 (Iff (Neg (pa_iter B n p))
    (pa_dia_iter B n (Neg p))).
Proof.
  intros A L0 L Hclass0 Hweak B Hext n.
  induction n as [|n IH]; intro p; cbn [pa_iter pa_dia_iter].
  - apply (logic_classical_tautology Hclass0).
    intro rho. unfold Iff, And, Neg. simpl. tauto.
  - set (x := generic_modal_iter (pa_box B) n p).
    set (y := generic_modal_iter (pa_dia B) n (Neg p)).
    pose proof (IH p) as Hnegx_y.
    assert (Hx_negy : L0 (Iff x (Neg y))).
    { eapply pa_tautology1; [exact Hclass0 | | exact Hnegx_y].
      intro rho. unfold Iff, And, Neg. simpl. tauto. }
    pose proof (pa_extensional Hext (Hweak _ Hx_negy)) as Hbox.
    eapply pa_tautology1; [exact Hclass0 | | exact Hbox].
    intro rho. unfold Iff, And, pa_dia, Neg. simpl. tauto.
Qed.

(** Every iteration entails its successor.  At zero this is ex falso; at a
    positive index it is exactly D3. *)
Lemma pa_iterated_bottom_step : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (B : pa_provability L0 L),
  pa_hbl3 B -> forall n,
  L (Imp (pa_iter B n Bottom) (pa_iter B (S n) Bottom)).
Proof.
  intros A L0 L Hclass Hweak B H3 [|n].
  - apply (logic_classical_tautology Hclass).
    intro rho. unfold pa_iter. cbn. tauto.
  - unfold pa_iter. cbn. apply Hweak. exact (pa_D3 H3 _).
Qed.

(** The source assumes full HBL.  Only D3 is needed: chaining the preceding
    one-step lemma gives arbitrary monotonicity. *)
Theorem pa_box_bottom_monotone : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (B : pa_provability L0 L),
  pa_hbl3 B -> forall n m, n <= m ->
  L (Imp (pa_iter B n Bottom) (pa_iter B m Bottom)).
Proof.
  intros A L0 L Hclass Hweak B H3 n m Hnm.
  assert (Hplus : forall k,
      L (Imp (pa_iter B n Bottom) (pa_iter B (n + k) Bottom))).
  { intro k. induction k as [|k IH].
    - rewrite Nat.add_0_r.
      apply (logic_classical_tautology Hclass).
      intro rho. simpl. tauto.
    - replace (n + S k) with (S (n + k)) by lia.
      exact (logic_imp_trans Hclass IH
        (pa_iterated_bottom_step Hclass Hweak H3 (n + k))). }
  replace m with (n + (m - n)) by lia.
  apply Hplus.
Qed.

Theorem pa_iterated_bottom_unprovable : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_kreisel B -> logic_consistent L ->
  forall n, ~ L (pa_iter B n Bottom).
Proof.
  intros A L0 L Hclass B HK Hconsistent n.
  induction n as [|n IH].
  - exact (logic_no_bot Hclass Hconsistent).
  - intro Hbox. apply IH. apply (pa_KR HK).
    exact Hbox.
Qed.

Definition pa_height {A : Type} {L0 L : modal_logic_set A}
    (B : pa_provability L0 L) : enat :=
  enat_find (fun n => L (pa_iter B n Bottom)).

Lemma pa_height_eq_top_iff : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L),
  pa_height B = enat_top <->
  forall n, ~ L (pa_iter B n Bottom).
Proof. intros. apply enat_find_eq_top_iff. Qed.

Lemma pa_height_le_of_iterated_bottom : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L) n,
  L (pa_iter B n Bottom) ->
  enat_le (pa_height B) (enat_of_nat n).
Proof. intros. now apply enat_find_le. Qed.

Lemma pa_height_lt_pos_of_base_iterated_bottom : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L),
  (forall p, L0 (pa_box B p) -> L p) ->
  forall n, 0 < n -> L0 (pa_iter B n Bottom) ->
  enat_lt (pa_height B) (enat_of_nat n).
Proof.
  intros A L0 L B Hsound [|n] Hpos Hiter; [lia |].
  apply enat_lt_succ_of_le.
  apply pa_height_le_of_iterated_bottom.
  apply Hsound. exact Hiter.
Qed.

Theorem pa_height_le_iff_iterated_bottom : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (Hweak : logic_subset L0 L) (B : pa_provability L0 L),
  pa_hbl3 B -> forall n,
  enat_le (pa_height B) (enat_of_nat n) <->
  L (pa_iter B n Bottom).
Proof.
  intros A L0 L Hclass Hweak B H3 n. split.
  - intro Hle.
    destruct (@enat_exists_of_find_le
      (fun m => L (pa_iter B m Bottom)) n Hle)
      as [m [Hmn Hm]].
    eapply logic_modus_ponens; [exact Hclass | | exact Hm].
    exact (pa_box_bottom_monotone Hclass Hweak H3 Hmn).
  - apply pa_height_le_of_iterated_bottom.
Qed.

Theorem pa_height_eq_top_of_kreisel_consistent : forall (A : Type)
    (L0 L : modal_logic_set A) (Hclass : classical_logic L)
    (B : pa_provability L0 L),
  pa_kreisel B -> logic_consistent L ->
  pa_height B = enat_top.
Proof.
  intros A L0 L Hclass B HK Hconsistent.
  apply pa_height_eq_top_iff.
  exact (pa_iterated_bottom_unprovable Hclass HK Hconsistent).
Qed.

Theorem pa_height_eq_zero_of_inconsistent : forall (A : Type)
    (L0 L : modal_logic_set A) (B : pa_provability L0 L),
  logic_inconsistent L ->
  pa_height B = enat_of_nat 0.
Proof.
  intros A L0 L B Hinc. unfold pa_height.
  apply enat_find_eq_zero. exact (Hinc Bottom).
Qed.
