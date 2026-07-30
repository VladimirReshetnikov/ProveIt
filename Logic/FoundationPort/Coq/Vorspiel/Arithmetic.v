(** Executable arithmetic truth values and bounded universal quantification. *)

From Stdlib Require Import Arith.Arith Lia Logic.FunctionalExtensionality
  Vectors.Fin.
From Foundation.Vorspiel Require Import Matrix Part.

Definition nat_truth_eq (n m : nat) : nat :=
  if Nat.eq_dec n m then 1 else 0.

Definition nat_truth_lt (n m : nat) : nat :=
  if lt_dec n m then 1 else 0.

Definition nat_truth_le (n m : nat) : nat :=
  if le_dec n m then 1 else 0.

Definition nat_truth_dvd (n m : nat) : nat :=
  if Nat.eq_dec n 0 then nat_truth_eq m 0
  else nat_truth_eq (m mod n) 0.

Lemma nat_positive_of_eq_one : forall n, n = 1 -> 0 < n.
Proof. intros n ->. lia. Qed.

Lemma nat_truth_eq_positive_iff : forall n m,
  0 < nat_truth_eq n m <-> n = m.
Proof. intros n m. unfold nat_truth_eq. destruct (Nat.eq_dec n m); lia. Qed.

Lemma nat_truth_lt_positive_iff : forall n m,
  0 < nat_truth_lt n m <-> n < m.
Proof. intros n m. unfold nat_truth_lt. destruct (lt_dec n m); lia. Qed.

Lemma nat_truth_le_positive_iff : forall n m,
  0 < nat_truth_le n m <-> n <= m.
Proof. intros n m. unfold nat_truth_le. destruct (le_dec n m); lia. Qed.

Lemma nat_truth_dvd_positive_iff : forall n m,
  0 < nat_truth_dvd n m <-> Nat.divide n m.
Proof.
  intros n m. unfold nat_truth_dvd.
  destruct (Nat.eq_dec n 0) as [-> | Hn].
  - rewrite nat_truth_eq_positive_iff. split.
    + intro H. subst m. now exists 0.
    + intros [k Hk]. now rewrite Nat.mul_0_r in Hk.
  - rewrite nat_truth_eq_positive_iff, Nat.mod_divide by exact Hn.
    reflexivity.
Qed.

Definition nat_truth_inv (n : nat) : nat := nat_truth_eq n 0.
Definition nat_truth_pos (n : nat) : nat := nat_truth_lt 0 n.
Definition nat_truth_and (n m : nat) : nat := nat_truth_lt 0 (n * m).
Definition nat_truth_or (n m : nat) : nat := nat_truth_lt 0 (n + m).

Lemma nat_truth_inv_zero : nat_truth_inv 0 = 1.
Proof. reflexivity. Qed.

Lemma nat_truth_inv_eq_zero_iff : forall n,
  nat_truth_inv n = 0 <-> 0 < n.
Proof.
  intro n. unfold nat_truth_inv, nat_truth_eq.
  destruct (Nat.eq_dec n 0); lia.
Qed.

Lemma nat_truth_inv_nonzero : forall n,
  n <> 0 -> nat_truth_inv n = 0.
Proof. intros n H. unfold nat_truth_inv, nat_truth_eq. now destruct Nat.eq_dec. Qed.

Lemma nat_truth_pos_zero : nat_truth_pos 0 = 0.
Proof. reflexivity. Qed.

Lemma nat_truth_pos_nonzero : forall n,
  n <> 0 -> nat_truth_pos n = 1.
Proof. intros n H. unfold nat_truth_pos, nat_truth_lt. destruct lt_dec; lia. Qed.

Lemma nat_truth_and_positive_iff : forall n m,
  0 < nat_truth_and n m <-> 0 < n /\ 0 < m.
Proof.
  intros n m. unfold nat_truth_and. rewrite nat_truth_lt_positive_iff.
  nia.
Qed.

Lemma nat_truth_or_positive_iff : forall n m,
  0 < nat_truth_or n m <-> 0 < n \/ 0 < m.
Proof.
  intros n m. unfold nat_truth_or. rewrite nat_truth_lt_positive_iff.
  lia.
Qed.

Lemma nat_truth_inv_positive_iff : forall n,
  0 < nat_truth_inv n <-> ~ 0 < n.
Proof. intro n. unfold nat_truth_inv. rewrite nat_truth_eq_positive_iff. lia. Qed.

Lemma nat_truth_pos_positive_iff : forall n,
  0 < nat_truth_pos n <-> 0 < n.
Proof. intro n. apply nat_truth_lt_positive_iff. Qed.

Fixpoint nat_bounded_all (n : nat) (phi : nat -> nat) : nat :=
  match n with
  | 0 => 1
  | S k => nat_truth_and (nat_truth_pos (phi k)) (nat_bounded_all k phi)
  end.

Theorem nat_bounded_all_positive_iff : forall n phi,
  0 < nat_bounded_all n phi <->
  forall m, m < n -> 0 < phi m.
Proof.
  induction n as [|n IH]; intro phi; simpl.
  - split; [intros _ m H; lia | intros; lia].
  - rewrite nat_truth_and_positive_iff,
      nat_truth_pos_positive_iff, IH.
    split.
    + intros [Hn Hall] m Hm. destruct (Nat.eq_dec m n) as [-> | Hne].
      * exact Hn.
      * apply Hall. lia.
    + intro Hall. split.
      * apply Hall. lia.
      * intros m Hm. apply Hall. lia.
Qed.

Lemma nat_bounded_all_boolean : forall n phi,
  nat_bounded_all n phi = 0 \/ nat_bounded_all n phi = 1.
Proof.
  induction n as [|n IH]; intro phi; simpl; [now right |].
  unfold nat_truth_and, nat_truth_lt.
  destruct lt_dec; [now right | now left].
Qed.

Lemma nat_truth_pos_eq_zero_iff : forall n,
  nat_truth_pos n = 0 <-> n = 0.
Proof.
  intro n. unfold nat_truth_pos, nat_truth_lt.
  destruct (lt_dec 0 n); lia.
Qed.

Lemma nat_truth_and_eq_zero_iff : forall n m,
  nat_truth_and n m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m. unfold nat_truth_and, nat_truth_lt.
  destruct (lt_dec 0 (n * m)) as [Hpos | Hnpos].
  - split; [discriminate | intros [-> | ->]; simpl in Hpos; lia].
  - split; [|intro; reflexivity].
    intro Hzero. apply Nat.eq_mul_0. lia.
Qed.

Theorem nat_bounded_all_eq_zero_iff : forall n phi,
  nat_bounded_all n phi = 0 <->
  exists m, m < n /\ phi m = 0.
Proof.
  induction n as [|n IH]; intro phi; simpl.
  - split; [discriminate | intros [m [Hm _]]; lia].
  - rewrite nat_truth_and_eq_zero_iff,
      nat_truth_pos_eq_zero_iff, IH.
    split.
    + intros [Hn | [m [Hm Hmzero]]].
      * exists n. split; [lia | exact Hn].
      * exists m. split; [lia | exact Hmzero].
    + intros [m [Hm Hzero]].
      destruct (Nat.eq_dec m n) as [-> | Hne].
      * now left.
      * right. exists m. split; [lia | exact Hzero].
Qed.

Theorem nat_bounded_all_eq_one_iff_positive : forall n phi,
  nat_bounded_all n phi = 1 <-> 0 < nat_bounded_all n phi.
Proof.
  intros n phi. destruct (nat_bounded_all_boolean n phi) as [-> | ->]; lia.
Qed.

(** The source's first partial-arithmetic closure calculus, stated directly
    over finite functions and the proof-relevant partial values from [Part]. *)
Definition arith_partial_function (n : nat) : Type :=
  (Fin.t n -> nat) -> partial_value nat.

Definition arith_partial_comp {m n}
    (f : arith_partial_function n)
    (g : Fin.t n -> arith_partial_function m) :
    arith_partial_function m :=
  fun v => partial_bind
    (fin_partial_product (fun i => g i v)) f.

Definition arith_find_on {n} (f : (Fin.t (S n) -> nat) -> nat)
    (v : Fin.t n -> nat) : partial_value nat :=
  partial_find_zero (fun k => f (matrix_vec_cons k v)).

Inductive arith_part1 : forall n, arith_partial_function n -> Prop :=
| arith_part1_zero : forall n,
    arith_part1 n (fun _ => partial_some 0)
| arith_part1_one : forall n,
    arith_part1 n (fun _ => partial_some 1)
| arith_part1_add : forall n (i j : Fin.t n),
    arith_part1 n (fun v => partial_some (v i + v j))
| arith_part1_mul : forall n (i j : Fin.t n),
    arith_part1 n (fun v => partial_some (v i * v j))
| arith_part1_proj : forall n (i : Fin.t n),
    arith_part1 n (fun v => partial_some (v i))
| arith_part1_equal : forall n (i j : Fin.t n),
    arith_part1 n (fun v => partial_some (nat_truth_eq (v i) (v j)))
| arith_part1_lt : forall n (i j : Fin.t n),
    arith_part1 n (fun v => partial_some (nat_truth_lt (v i) (v j)))
| arith_part1_comp : forall m n (f : arith_partial_function n)
    (g : Fin.t n -> arith_partial_function m),
    arith_part1 n f ->
    (forall i, arith_part1 m (g i)) ->
    arith_part1 m (arith_partial_comp f g)
| arith_part1_find : forall n (f : (Fin.t (S n) -> nat) -> nat),
    arith_part1 (S n) (fun v => partial_some (f v)) ->
    arith_part1 n (arith_find_on f)
| arith_part1_ext : forall n (f g : arith_partial_function n),
    arith_part1 n f ->
    (forall v x, partial_member (f v) x <-> partial_member (g v) x) ->
    arith_part1 n g.

Definition arithmetic1 {n} (f : (Fin.t n -> nat) -> nat) : Prop :=
  arith_part1 n (fun v => partial_some (f v)).

Lemma arith_find_on_member_iff : forall n
    (f : (Fin.t (S n) -> nat) -> nat) (v : Fin.t n -> nat) k,
  partial_member (arith_find_on f v) k <->
  f (matrix_vec_cons k v) = 0 /\
  forall m, m < k -> f (matrix_vec_cons m v) <> 0.
Proof. reflexivity. Qed.

Lemma arith_partial_comp_some_member_iff : forall m n
    (f : (Fin.t n -> nat) -> nat)
    (g : Fin.t n -> (Fin.t m -> nat) -> nat)
    (v : Fin.t m -> nat) x,
  partial_member
    (arith_partial_comp (fun w => partial_some (f w))
      (fun i w => partial_some (g i w)) v) x <->
  x = f (fun i => g i v).
Proof.
  intros m n f g v x. unfold arith_partial_comp, partial_bind. simpl.
  split.
  - intros [w [Hw Hx]].
    assert (Heq : w = (fun i => g i v)).
    { apply functional_extensionality. intro i. exact (Hw i). }
    now subst w.
  - intro Hx. exists (fun i => g i v). split.
    + intro i. reflexivity.
    + exact Hx.
Qed.

Lemma arithmetic1_zero : forall n,
  @arithmetic1 n (fun _ => 0).
Proof. intro n. apply arith_part1_zero. Qed.

Lemma arithmetic1_one : forall n,
  @arithmetic1 n (fun _ => 1).
Proof. intro n. apply arith_part1_one. Qed.

Lemma arithmetic1_add : forall n (i j : Fin.t n),
  arithmetic1 (fun v => v i + v j).
Proof. intros. apply arith_part1_add. Qed.

Lemma arithmetic1_mul : forall n (i j : Fin.t n),
  arithmetic1 (fun v => v i * v j).
Proof. intros. apply arith_part1_mul. Qed.

Lemma arithmetic1_proj : forall n (i : Fin.t n),
  arithmetic1 (fun v => v i).
Proof. intros. apply arith_part1_proj. Qed.

Lemma arithmetic1_equal : forall n (i j : Fin.t n),
  arithmetic1 (fun v => nat_truth_eq (v i) (v j)).
Proof. intros. apply arith_part1_equal. Qed.

Lemma arithmetic1_lt : forall n (i j : Fin.t n),
  arithmetic1 (fun v => nat_truth_lt (v i) (v j)).
Proof. intros. apply arith_part1_lt. Qed.

Theorem arithmetic1_comp : forall m n
    (f : (Fin.t n -> nat) -> nat)
    (g : Fin.t n -> (Fin.t m -> nat) -> nat),
  arithmetic1 f ->
  (forall i, arithmetic1 (g i)) ->
  arithmetic1 (fun v => f (fun i => g i v)).
Proof.
  intros m n f g Hf Hg. unfold arithmetic1 in *.
  eapply arith_part1_ext.
  - apply arith_part1_comp.
    + exact Hf.
    + exact Hg.
  - intros v x. rewrite arith_partial_comp_some_member_iff.
    reflexivity.
Qed.

Definition arithmetic1_unary (f : nat -> nat) : Prop :=
  @arithmetic1 1 (fun v => f (v Fin.F1)).

Definition arithmetic1_binary (f : nat -> nat -> nat) : Prop :=
  @arithmetic1 2 (fun v => f (v Fin.F1) (v (Fin.FS Fin.F1))).

Theorem arithmetic1_comp1 : forall n (f : nat -> nat)
    (g : (Fin.t n -> nat) -> nat),
  arithmetic1_unary f -> arithmetic1 g ->
  arithmetic1 (fun v => f (g v)).
Proof.
  intros n f g Hf Hg. unfold arithmetic1_unary in Hf.
  eapply arithmetic1_comp with
    (f := fun w => f (w Fin.F1)) (g := fun _ => g).
  - exact Hf.
  - intro. exact Hg.
Qed.

Theorem arithmetic1_comp2 : forall n (f : nat -> nat -> nat)
    (g h : (Fin.t n -> nat) -> nat),
  arithmetic1_binary f -> arithmetic1 g -> arithmetic1 h ->
  arithmetic1 (fun v => f (g v) (h v)).
Proof.
  intros n f g h Hf Hg Hh. unfold arithmetic1_binary in Hf.
  eapply arithmetic1_comp with
    (f := fun w => f (w Fin.F1) (w (Fin.FS Fin.F1)))
    (g := fun i => @Fin.caseS' 1 i
      (fun _ => (Fin.t n -> nat) -> nat) g (fun _ => h)).
  - exact Hf.
  - intro i. refine (@Fin.caseS' 1 i
      (fun j => arithmetic1 (@Fin.caseS' 1 j
        (fun _ => (Fin.t n -> nat) -> nat) g (fun _ => h))) Hg _).
    intro j. exact Hh.
Qed.

Lemma arithmetic1_succ : arithmetic1_unary S.
Proof.
  unfold arithmetic1_unary.
  eapply arith_part1_ext.
  - unfold arithmetic1.
    eapply arithmetic1_comp2 with (f := Nat.add)
      (g := fun v : Fin.t 1 -> nat => v Fin.F1)
      (h := fun _ : Fin.t 1 -> nat => 1).
    + unfold arithmetic1_binary. apply arithmetic1_add.
    + apply arithmetic1_proj.
    + apply arithmetic1_one.
  - intros v x. simpl. split; intro H; subst x; f_equal; lia.
Qed.

Theorem arithmetic1_const : forall n k,
  @arithmetic1 n (fun _ => k).
Proof.
  intros n k. induction k as [|k IH].
  - apply arithmetic1_zero.
  - change (arithmetic1 (fun _ : Fin.t n -> nat => S k)).
    apply arithmetic1_comp1; [apply arithmetic1_succ | exact IH].
Qed.

Lemma arithmetic1_inv : arithmetic1_unary nat_truth_inv.
Proof.
  unfold arithmetic1_unary, nat_truth_inv.
  eapply arithmetic1_comp2.
  - unfold arithmetic1_binary. apply arithmetic1_equal.
  - apply arithmetic1_proj.
  - apply arithmetic1_zero.
Qed.

Lemma arithmetic1_pos : arithmetic1_unary nat_truth_pos.
Proof.
  unfold arithmetic1_unary, nat_truth_pos.
  eapply arithmetic1_comp2.
  - unfold arithmetic1_binary. apply arithmetic1_lt.
  - apply arithmetic1_zero.
  - apply arithmetic1_proj.
Qed.

Lemma arithmetic1_and : arithmetic1_binary nat_truth_and.
Proof.
  unfold arithmetic1_binary, nat_truth_and.
  eapply arithmetic1_comp2.
  - unfold arithmetic1_binary. apply arithmetic1_lt.
  - apply arithmetic1_zero.
  - apply arithmetic1_mul.
Qed.

Lemma arithmetic1_or : arithmetic1_binary nat_truth_or.
Proof.
  unfold arithmetic1_binary, nat_truth_or.
  eapply arithmetic1_comp2.
  - unfold arithmetic1_binary. apply arithmetic1_lt.
  - apply arithmetic1_zero.
  - apply arithmetic1_add.
Qed.
