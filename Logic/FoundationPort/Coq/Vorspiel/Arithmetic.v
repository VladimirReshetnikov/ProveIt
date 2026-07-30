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

Lemma nat_truth_le_as_or : forall n m,
  nat_truth_le n m =
  nat_truth_or (nat_truth_lt n m) (nat_truth_eq n m).
Proof.
  intros n m.
  unfold nat_truth_or, nat_truth_lt, nat_truth_eq, nat_truth_le.
  destruct (lt_dec n m); destruct (Nat.eq_dec n m);
    destruct (le_dec n m); cbn; repeat destruct lt_dec; lia.
Qed.

Lemma arithmetic1_le : arithmetic1_binary nat_truth_le.
Proof.
  unfold arithmetic1_binary.
  eapply arith_part1_ext.
  - unfold arithmetic1.
    eapply arithmetic1_comp2 with (f := nat_truth_or)
      (g := fun v : Fin.t 2 -> nat =>
        nat_truth_lt (v Fin.F1) (v (Fin.FS Fin.F1)))
      (h := fun v : Fin.t 2 -> nat =>
        nat_truth_eq (v Fin.F1) (v (Fin.FS Fin.F1))).
    + exact arithmetic1_or.
    + apply arithmetic1_lt.
    + apply arithmetic1_equal.
  - intros v x. simpl.
    rewrite <- nat_truth_le_as_or. reflexivity.
Qed.

Lemma nat_truth_if_positive : forall c x y,
  nat_truth_pos c * x + nat_truth_inv c * y =
  if lt_dec 0 c then x else y.
Proof.
  intros c x y.
  unfold nat_truth_pos, nat_truth_inv, nat_truth_lt, nat_truth_eq.
  destruct (lt_dec 0 c) as [Hc | Hc].
  - destruct (Nat.eq_dec c 0); [lia | cbn; lia].
  - destruct (Nat.eq_dec c 0); [subst; cbn; lia | lia].
Qed.

Theorem arithmetic1_if_positive : forall n
    (f g h : (Fin.t n -> nat) -> nat),
  arithmetic1 f -> arithmetic1 g -> arithmetic1 h ->
  arithmetic1 (fun v => if lt_dec 0 (f v) then g v else h v).
Proof.
  intros n f g h Hf Hg Hh.
  pose proof (@arithmetic1_comp1 n nat_truth_pos f
    arithmetic1_pos Hf) as Hpos.
  pose proof (@arithmetic1_comp1 n nat_truth_inv f
    arithmetic1_inv Hf) as Hinv.
  assert (Hmul : arithmetic1_binary Nat.mul).
  { unfold arithmetic1_binary. apply arithmetic1_mul. }
  assert (Hadd : arithmetic1_binary Nat.add).
  { unfold arithmetic1_binary. apply arithmetic1_add. }
  pose proof (@arithmetic1_comp2 n Nat.mul
    (fun v => nat_truth_pos (f v)) g Hmul Hpos Hg) as Hleft.
  pose proof (@arithmetic1_comp2 n Nat.mul
    (fun v => nat_truth_inv (f v)) h Hmul Hinv Hh) as Hright.
  eapply arith_part1_ext.
  - unfold arithmetic1.
    exact (@arithmetic1_comp2 n Nat.add
      (fun v => nat_truth_pos (f v) * g v)
      (fun v => nat_truth_inv (f v) * h v)
      Hadd Hleft Hright).
  - intros v x. simpl. now rewrite nat_truth_if_positive.
Qed.

Definition arith_find_positive_on {n}
    (f : (Fin.t (S n) -> nat) -> nat) (v : Fin.t n -> nat) :
    partial_value nat :=
  partial_find_zero
    (fun k => nat_truth_inv (f (matrix_vec_cons k v))).

Theorem arith_part1_find_positive : forall n
    (f : (Fin.t (S n) -> nat) -> nat),
  arithmetic1 f -> arith_part1 n (arith_find_positive_on f).
Proof.
  intros n f Hf.
  change (arith_part1 n (arith_find_on (fun v => nat_truth_inv (f v)))).
  apply arith_part1_find.
  unfold arithmetic1.
  apply arithmetic1_comp1; [exact arithmetic1_inv | exact Hf].
Qed.

Lemma arith_find_positive_on_member_iff : forall n
    (f : (Fin.t (S n) -> nat) -> nat) (v : Fin.t n -> nat) k,
  partial_member (arith_find_positive_on f v) k <->
  0 < f (matrix_vec_cons k v) /\
  forall m, m < k -> ~ 0 < f (matrix_vec_cons m v).
Proof.
  intros n f v k. unfold arith_find_positive_on.
  rewrite partial_find_zero_member_iff.
  split.
  - intros [Hk Hleast]. split.
    + now apply nat_truth_inv_eq_zero_iff in Hk.
    + intros m Hm Hpos. apply (Hleast m Hm).
      now apply nat_truth_inv_eq_zero_iff.
  - intros [Hk Hleast]. split.
    + now apply nat_truth_inv_eq_zero_iff.
    + intros m Hm Hinv.
      apply nat_truth_inv_eq_zero_iff in Hinv.
      exact (Hleast m Hm Hinv).
Qed.

Definition nat_sub_test (k a b : nat) : nat :=
  nat_truth_or
    (nat_truth_eq (k + b) a)
    (nat_truth_and (nat_truth_lt a b) (nat_truth_eq k 0)).

Lemma nat_sub_test_positive_iff : forall k a b,
  0 < nat_sub_test k a b <->
  k + b = a \/ (a < b /\ k = 0).
Proof.
  intros k a b. unfold nat_sub_test.
  rewrite nat_truth_or_positive_iff, nat_truth_eq_positive_iff,
    nat_truth_and_positive_iff, nat_truth_lt_positive_iff,
    nat_truth_eq_positive_iff.
  tauto.
Qed.

Lemma nat_sub_least_test : forall a b x,
  x = a - b <->
  (x + b = a \/ (a < b /\ x = 0)) /\
  forall m, m < x -> ~ (m + b = a \/ (a < b /\ m = 0)).
Proof.
  intros a b x. split.
  - intro Hx. subst x. split.
    + destruct (le_dec b a) as [Hba | Hba].
      * left. now apply Nat.sub_add.
      * right. split; [lia | apply Nat.sub_0_le; lia].
    + intros m Hm [Heq | [Hab Hzero]].
      * assert (m + b < a) by lia. lia.
      * subst m. lia.
  - intros [[Heq | [Hab Hzero]] _].
    + assert (b <= a) by lia. lia.
    + subst x. apply eq_sym, Nat.sub_0_le. lia.
Qed.

Definition nat_sub_test_vector (v : Fin.t 3 -> nat) : nat :=
  nat_sub_test
    (v Fin.F1)
    (v (Fin.FS Fin.F1))
    (v (Fin.FS (Fin.FS Fin.F1))).

Lemma arithmetic1_sub_test : arithmetic1 nat_sub_test_vector.
Proof.
  unfold nat_sub_test_vector, nat_sub_test.
  eapply arithmetic1_comp2 with (f := nat_truth_or).
  - exact arithmetic1_or.
  - eapply arithmetic1_comp2 with (f := nat_truth_eq).
    + apply arithmetic1_equal.
    + eapply arithmetic1_comp2 with (f := Nat.add).
      * unfold arithmetic1_binary. apply arithmetic1_add.
      * apply arithmetic1_proj.
      * apply arithmetic1_proj.
    + apply arithmetic1_proj.
  - eapply arithmetic1_comp2 with (f := nat_truth_and).
    + exact arithmetic1_and.
    + eapply arithmetic1_comp2 with (f := nat_truth_lt).
      * apply arithmetic1_lt.
      * apply arithmetic1_proj.
      * apply arithmetic1_proj.
    + eapply arithmetic1_comp2 with (f := nat_truth_eq).
      * apply arithmetic1_equal.
      * apply arithmetic1_proj.
      * apply arithmetic1_zero.
Qed.

Theorem arithmetic1_sub : arithmetic1_binary Nat.sub.
Proof.
  unfold arithmetic1_binary, arithmetic1.
  eapply arith_part1_ext with
    (f := arith_find_positive_on nat_sub_test_vector).
  - apply arith_part1_find_positive. exact arithmetic1_sub_test.
  - intros v x. rewrite arith_find_positive_on_member_iff.
    change
      ((0 < nat_sub_test x (v Fin.F1) (v (Fin.FS Fin.F1)) /\
        forall m, m < x ->
          ~ 0 < nat_sub_test m (v Fin.F1) (v (Fin.FS Fin.F1))) <->
       x = v Fin.F1 - v (Fin.FS Fin.F1)).
    rewrite nat_sub_test_positive_iff.
    setoid_rewrite nat_sub_test_positive_iff.
    apply iff_sym.
    exact (nat_sub_least_test
      (v Fin.F1) (v (Fin.FS Fin.F1)) x).
Qed.

Definition nat_pair (a b : nat) : nat :=
  if lt_dec a b then b * b + a else a * a + a + b.

Lemma nat_truth_lt_branch : forall a b x y : nat,
  (if lt_dec 0 (nat_truth_lt a b) then x else y) =
  (if lt_dec a b then x else y).
Proof.
  intros a b x y. unfold nat_truth_lt.
  destruct (lt_dec a b); cbn; repeat destruct lt_dec; lia.
Qed.

Theorem arithmetic1_pair : arithmetic1_binary nat_pair.
Proof.
  unfold arithmetic1_binary.
  assert (Hcond : arithmetic1 (fun v : Fin.t 2 -> nat =>
      nat_truth_lt (v Fin.F1) (v (Fin.FS Fin.F1)))).
  { apply arithmetic1_lt. }
  assert (Hthen : arithmetic1 (fun v : Fin.t 2 -> nat =>
      v (Fin.FS Fin.F1) * v (Fin.FS Fin.F1) + v Fin.F1)).
  { eapply arithmetic1_comp2 with (f := Nat.add).
    - unfold arithmetic1_binary. apply arithmetic1_add.
    - eapply arithmetic1_comp2 with (f := Nat.mul).
      + unfold arithmetic1_binary. apply arithmetic1_mul.
      + apply arithmetic1_proj.
      + apply arithmetic1_proj.
    - apply arithmetic1_proj. }
  assert (Helse : arithmetic1 (fun v : Fin.t 2 -> nat =>
      v Fin.F1 * v Fin.F1 + v Fin.F1 + v (Fin.FS Fin.F1))).
  { eapply arithmetic1_comp2 with (f := Nat.add).
    - unfold arithmetic1_binary. apply arithmetic1_add.
    - eapply arithmetic1_comp2 with (f := Nat.add).
      + unfold arithmetic1_binary. apply arithmetic1_add.
      + eapply arithmetic1_comp2 with (f := Nat.mul).
        * unfold arithmetic1_binary. apply arithmetic1_mul.
        * apply arithmetic1_proj.
        * apply arithmetic1_proj.
      + apply arithmetic1_proj.
    - apply arithmetic1_proj. }
  eapply arith_part1_ext.
  - unfold arithmetic1.
    exact (@arithmetic1_if_positive 2 _ _ _ Hcond Hthen Helse).
  - intros v x. simpl. unfold nat_pair.
    now rewrite nat_truth_lt_branch.
Qed.

Definition nat_sqrt_test (k a : nat) : nat :=
  nat_truth_and
    (nat_truth_le (k * k) a)
    (nat_truth_lt a (S k * S k)).

Lemma nat_sqrt_test_positive_iff : forall k a,
  0 < nat_sqrt_test k a <->
  k * k <= a /\ a < S k * S k.
Proof.
  intros k a. unfold nat_sqrt_test.
  rewrite nat_truth_and_positive_iff, nat_truth_le_positive_iff,
    nat_truth_lt_positive_iff.
  tauto.
Qed.

Lemma nat_sqrt_least_test : forall a x,
  x = Nat.sqrt a <->
  (x * x <= a /\ a < S x * S x) /\
  forall m, m < x -> ~ (m * m <= a /\ a < S m * S m).
Proof.
  intros a x. split.
  - intro Hx. subst x.
    destruct (Nat.sqrt_specif a) as [Hlower Hupper].
    split; [tauto |].
    intros m Hm [_ Hmupper].
    assert (S m <= Nat.sqrt a) by lia.
    nia.
  - intros [[Hxlower Hxupper] _].
    destruct (Nat.sqrt_specif a) as [Hlower Hupper].
    nia.
Qed.

Definition nat_sqrt_test_vector (v : Fin.t 2 -> nat) : nat :=
  nat_sqrt_test (v Fin.F1) (v (Fin.FS Fin.F1)).

Lemma arithmetic1_sqrt_test : arithmetic1 nat_sqrt_test_vector.
Proof.
  unfold nat_sqrt_test_vector, nat_sqrt_test.
  eapply arithmetic1_comp2 with (f := nat_truth_and).
  - exact arithmetic1_and.
  - eapply arithmetic1_comp2 with (f := nat_truth_le).
    + exact arithmetic1_le.
    + eapply arithmetic1_comp2 with (f := Nat.mul).
      * unfold arithmetic1_binary. apply arithmetic1_mul.
      * apply arithmetic1_proj.
      * apply arithmetic1_proj.
    + apply arithmetic1_proj.
  - eapply arithmetic1_comp2 with (f := nat_truth_lt).
    + apply arithmetic1_lt.
    + apply arithmetic1_proj.
    + eapply arithmetic1_comp2 with (f := Nat.mul).
      * unfold arithmetic1_binary. apply arithmetic1_mul.
      * eapply arithmetic1_comp1 with (f := S).
        -- exact arithmetic1_succ.
        -- apply arithmetic1_proj.
      * eapply arithmetic1_comp1 with (f := S).
        -- exact arithmetic1_succ.
        -- apply arithmetic1_proj.
Qed.

Theorem arithmetic1_sqrt : arithmetic1_unary Nat.sqrt.
Proof.
  unfold arithmetic1_unary, arithmetic1.
  eapply arith_part1_ext with
    (f := arith_find_positive_on nat_sqrt_test_vector).
  - apply arith_part1_find_positive. exact arithmetic1_sqrt_test.
  - intros v x. rewrite arith_find_positive_on_member_iff.
    change
      ((0 < nat_sqrt_test x (v Fin.F1) /\
        forall m, m < x -> ~ 0 < nat_sqrt_test m (v Fin.F1)) <->
       x = Nat.sqrt (v Fin.F1)).
    rewrite nat_sqrt_test_positive_iff.
    setoid_rewrite nat_sqrt_test_positive_iff.
    apply iff_sym. exact (nat_sqrt_least_test (v Fin.F1) x).
Qed.

Theorem arithmetic1_if_lt : forall n
    (f g h k : (Fin.t n -> nat) -> nat),
  arithmetic1 f -> arithmetic1 g -> arithmetic1 h -> arithmetic1 k ->
  arithmetic1 (fun v => if lt_dec (f v) (g v) then h v else k v).
Proof.
  intros n f g h k Hf Hg Hh Hk.
  assert (Hcond : arithmetic1 (fun v => nat_truth_lt (f v) (g v))).
  { eapply arithmetic1_comp2; [apply arithmetic1_lt | exact Hf | exact Hg]. }
  eapply arith_part1_ext.
  - unfold arithmetic1.
    exact (@arithmetic1_if_positive n _ h k Hcond Hh Hk).
  - intros v x. simpl. now rewrite nat_truth_lt_branch.
Qed.

Definition nat_square_remainder (n : nat) : nat :=
  n - Nat.sqrt n * Nat.sqrt n.

Lemma arithmetic1_square_remainder :
  arithmetic1_unary nat_square_remainder.
Proof.
  unfold arithmetic1_unary, nat_square_remainder.
  eapply arithmetic1_comp2 with (f := Nat.sub).
  - exact arithmetic1_sub.
  - apply arithmetic1_proj.
  - eapply arithmetic1_comp2 with (f := Nat.mul).
    + unfold arithmetic1_binary. apply arithmetic1_mul.
    + exact arithmetic1_sqrt.
    + exact arithmetic1_sqrt.
Qed.

Definition nat_unpair1 (n : nat) : nat :=
  if lt_dec (nat_square_remainder n) (Nat.sqrt n)
  then nat_square_remainder n
  else Nat.sqrt n.

Definition nat_unpair2 (n : nat) : nat :=
  if lt_dec (nat_square_remainder n) (Nat.sqrt n)
  then Nat.sqrt n
  else nat_square_remainder n - Nat.sqrt n.

Definition nat_unpair (n : nat) : nat * nat :=
  (nat_unpair1 n, nat_unpair2 n).

Theorem arithmetic1_unpair1 : arithmetic1_unary nat_unpair1.
Proof.
  unfold arithmetic1_unary, nat_unpair1.
  eapply arithmetic1_if_lt.
  - exact arithmetic1_square_remainder.
  - exact arithmetic1_sqrt.
  - exact arithmetic1_square_remainder.
  - exact arithmetic1_sqrt.
Qed.

Theorem arithmetic1_unpair2 : arithmetic1_unary nat_unpair2.
Proof.
  unfold arithmetic1_unary, nat_unpair2.
  eapply arithmetic1_if_lt.
  - exact arithmetic1_square_remainder.
  - exact arithmetic1_sqrt.
  - exact arithmetic1_sqrt.
  - eapply arithmetic1_comp2 with (f := Nat.sub).
    + exact arithmetic1_sub.
    + exact arithmetic1_square_remainder.
    + exact arithmetic1_sqrt.
Qed.
