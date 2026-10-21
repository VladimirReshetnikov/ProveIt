(* Concrete zero-credit theorem for the ZC215 command codec.
   New kernel-checked development, 2026-10-21.
   Uses only the Coq standard library. No project endpoint is claimed. *)
From Coq Require Import Lists.List Arith.PeanoNat Arith.Cantor Lia.
Import ListNotations.

Module ConcretePrefixCredit.

Definition pair (a b : nat) := Cantor.to_nat (a,b).

Lemma pair_inj a b c d : pair a b = pair c d -> a = c /\ b = d.
Proof.
  unfold pair. intro H. apply Cantor.to_nat_inj in H. inversion H. auto.
Qed.

Lemma pair_ge_right a b : b <= pair a b.
Proof. pose proof (Cantor.to_nat_non_decreasing a b). unfold pair. lia. Qed.

Lemma pair_strict_left a b c : a < b -> pair a c < pair b c.
Proof.
  intro H. pose proof (Cantor.to_nat_spec a c).
  pose proof (Cantor.to_nat_spec b c). unfold pair. nia.
Qed.

Lemma pair_strict_right a b c : a < b -> pair c a < pair c b.
Proof.
  intro H. pose proof (Cantor.to_nat_spec c a).
  pose proof (Cantor.to_nat_spec c b). unfold pair. nia.
Qed.

Inductive command : Type :=
| Drop | Nip | Mp (x : nat) | Ax (c x y : nat).

(* Literal field order: DROP [0], NIP [1], MP [2,x], AX [c+3,y,x]. *)
Definition emit (k : command) (r : nat) : nat :=
  match k with
  | Drop => pair 0 r
  | Nip => pair 1 r
  | Mp x => pair 2 (pair x r)
  | Ax c x y => pair (c+3) (pair y (pair x r))
  end.

Lemma emit_ge k r : r <= emit k r.
Proof.
  destruct k; cbn [emit]; repeat match goal with
  | |- ?r <= pair ?a ?b => eapply Nat.le_trans; [|apply pair_ge_right]
  end; lia.
Qed.

Lemma emit_inj k l r s : emit k r = emit l s -> k = l /\ r = s.
Proof.
  destruct k, l; cbn [emit]; intro H;
    apply pair_inj in H as [Htag Hrest]; try discriminate; try lia.
  - auto.
  - auto.
  - apply pair_inj in Hrest as [-> ->]. auto.
  - apply pair_inj in Hrest as [-> Hrest].
    apply pair_inj in Hrest as [-> ->].
    assert (c = c0) by lia. subst. auto.
Qed.

Lemma emit_strict k r s : r < s -> emit k r < emit k s.
Proof.
  destruct k; cbn [emit]; intro H;
    repeat apply pair_strict_right; exact H.
Qed.

(* code [] = 0 is the termination marker. A nonempty word has code
   1 + raw index. This separates the final DROP from an empty tail. *)
Fixpoint code (w : list command) : nat :=
  match w with [] => 0 | k :: t => S (emit k (code t)) end.

Lemma code_inj w v : code w = code v -> w = v.
Proof.
  revert v. induction w as [|k w IH]; intros [|l v] H;
    cbn [code] in H; try discriminate; auto.
  injection H as H. apply emit_inj in H as [-> E].
  f_equal. now apply IH.
Qed.

Lemma code_positive w : w <> [] -> 0 < code w.
Proof. destruct w; cbn [code]; intros H; [contradiction|lia]. Qed.

Definition head_decode (n : nat) : command * nat :=
  let '(tag,r) := Cantor.of_nat n in
  match tag with
  | 0 => (Drop,r)
  | 1 => (Nip,r)
  | 2 => let '(x,s) := Cantor.of_nat r in (Mp x,s)
  | S (S (S c)) =>
      let '(y,s) := Cantor.of_nat r in
      let '(x,t) := Cantor.of_nat s in (Ax c x y,t)
  end.

Lemma head_decode_correct n k r : head_decode n = (k,r) -> emit k r = n.
Proof.
  unfold head_decode. destruct (Cantor.of_nat n) as [tag rest] eqn:E.
  pose proof (Cantor.cancel_to_of n) as Hn. rewrite E in Hn.
  change (pair tag rest = n) in Hn.
  destruct tag as [|[|[|c]]]; cbn; intro H.
  - injection H as Hk Hr. subst k r. exact Hn.
  - injection H as Hk Hr. subst k r. exact Hn.
  - destruct (Cantor.of_nat rest) as [x s] eqn:F.
    injection H as Hk Hrs. subst k r. change (pair 2 (pair x s) = n).
    pose proof (Cantor.cancel_to_of rest) as Hr. rewrite F in Hr.
    change (pair x s = rest) in Hr. now rewrite Hr.
  - destruct (Cantor.of_nat rest) as [y s] eqn:F.
    destruct (Cantor.of_nat s) as [x t] eqn:G.
    injection H as Hk Hrt. subst k r.
    change (pair (c+3) (pair y (pair x t)) = n).
    pose proof (Cantor.cancel_to_of rest) as Hr. rewrite F in Hr.
    pose proof (Cantor.cancel_to_of s) as Hs. rewrite G in Hs.
    change (pair y s = rest) in Hr.
    change (pair x t = s) in Hs. rewrite Hs, Hr.
    replace (c+3) with (S (S (S c))) by lia. exact Hn.
Qed.

Fixpoint decode_fuel (fuel n : nat) : list command :=
  match fuel with
  | 0 => []
  | S f =>
      let '(k,r) := head_decode n in
      k :: match r with 0 => [] | S q => decode_fuel f q end
  end.

Lemma decode_fuel_correct fuel n : n < fuel ->
  code (decode_fuel fuel n) = S n.
Proof.
  revert n. induction fuel as [|f IH]; intros n Hbound; [lia|].
  cbn [decode_fuel]. destruct (head_decode n) as [k r] eqn:E.
  pose proof (head_decode_correct n k r E) as Hn.
  pose proof (emit_ge k r) as Hr. destruct r as [|q].
  - cbn [code]. now rewrite Hn.
  - cbn [code]. rewrite IH; [now rewrite Hn|lia].
Qed.

Definition word (n : nat) := decode_fuel (S n) n.

Theorem code_word n : code (word n) = S n.
Proof. apply decode_fuel_correct. lia. Qed.

Lemma word_nonempty n : word n <> [].
Proof. intro H. pose proof (code_word n) as E. rewrite H in E. discriminate. Qed.

Definition raw (w : list command) := Nat.pred (code w).

Theorem word_raw w : w <> [] -> word (raw w) = w.
Proof.
  intro H. apply code_inj. rewrite code_word. unfold raw.
  pose proof (code_positive w H). lia.
Qed.

Theorem raw_word n : raw (word n) = n.
Proof. unfold raw. rewrite code_word. reflexivity. Qed.

Fixpoint replace_at (j : nat) (k : command) (w : list command) :=
  match j,w with
  | 0, _ :: t => k :: t
  | S i, h :: t => h :: replace_at i k t
  | _, [] => []
  end.

Lemma replace_nonempty j k w : w <> [] -> replace_at j k w <> [].
Proof. destruct j, w; cbn; intuition discriminate. Qed.

Lemma nth_replace j old k w : nth_error w j = Some old ->
  nth_error (replace_at j k w) j = Some k.
Proof.
  revert j. induction w as [|h t IH]; intros [|j] H;
    cbn in *; try discriminate; auto.
Qed.

Lemma replace_restore j old k w : nth_error w j = Some old ->
  replace_at j old (replace_at j k w) = w.
Proof.
  revert j. induction w as [|h t IH]; intros [|j] H;
    cbn in *; try discriminate.
  - inversion H. reflexivity.
  - f_equal. now apply IH.
Qed.

Lemma lower_code j w : nth_error w j = Some Nip ->
  code (replace_at j Drop w) < code w.
Proof.
  revert j. induction w as [|h t IH]; intros [|j] H;
    cbn in *; try discriminate.
  - inversion H. subst.
    change (S (pair 0 (code t)) < S (pair 1 (code t))).
    pose proof (pair_strict_left 0 1 (code t) ltac:(lia)). lia.
  - pose proof (emit_strict h _ _ (IH j H)). lia.
Qed.

Definition occurrence := (nat * nat)%type.
Definition Push (x : occurrence) := nth_error (word (fst x)) (snd x) = Some Drop.
Definition Pop (x : occurrence) := nth_error (word (fst x)) (snd x) = Some Nip.
Definition lower (x : occurrence) : occurrence :=
  (raw (replace_at (snd x) Drop (word (fst x))), snd x).

Lemma lower_word n j : word (fst (lower (n,j))) = replace_at j Drop (word n).
Proof. unfold lower; cbn. apply word_raw, replace_nonempty, word_nonempty. Qed.

Theorem lower_push x : Pop x -> Push (lower x).
Proof.
  destruct x as [n j].
  change (nth_error (word n) j = Some Nip ->
    nth_error (word (fst (lower (n,j)))) j = Some Drop).
  rewrite lower_word. apply nth_replace.
Qed.

Theorem lower_earlier x : Pop x -> fst (lower x) < fst x.
Proof.
  destruct x as [n j]. unfold Pop; cbn. intro H.
  pose proof (lower_code j (word n) H) as E. rewrite code_word in E.
  pose proof (code_positive (replace_at j Drop (word n))
    (replace_nonempty j Drop (word n) (word_nonempty n))) as Hpos.
  change (Nat.pred (code (replace_at j Drop (word n))) < n). lia.
Qed.

Theorem lower_injective x y : Pop x -> Pop y -> lower x = lower y -> x = y.
Proof.
  destruct x as [n j], y as [m i]. intros Hx Hy E.
  assert (j=i) as J by (injection E; auto). subst i.
  assert (fst (lower (n,j)) = fst (lower (m,j))) as F by now rewrite E.
  apply (f_equal word) in F. rewrite !lower_word in F.
  apply (f_equal (replace_at j Nip)) in F.
  unfold Pop in Hx, Hy; cbn in Hx, Hy.
  rewrite (replace_restore j Nip Drop (word n) Hx) in F.
  rewrite (replace_restore j Nip Drop (word m) Hy) in F.
  apply (f_equal raw) in F. rewrite !raw_word in F. subst. reflexivity.
Qed.

(* Every occurrence in every completed raw candidate, followed by a cut
   before position j of candidate n. Ordering does not affect counts. *)
Definition at_candidate n len : list occurrence :=
  map (fun j => (n,j)) (seq 0 len).

Lemma in_at_candidate n len m j :
  In (m,j) (at_candidate n len) <-> m=n /\ j<len.
Proof.
  unfold at_candidate. rewrite in_map_iff. split.
  - intros [i [E Hi]]. inversion E; subst. rewrite in_seq in Hi. lia.
  - intros [-> Hj]. exists j. split; [reflexivity|]. apply in_seq. lia.
Qed.

Fixpoint completed (n : nat) : list occurrence :=
  match n with
  | 0 => []
  | S m => completed m ++ at_candidate m (length (word m))
  end.

Lemma in_completed n m j :
  In (m,j) (completed n) <-> m<n /\ j<length (word m).
Proof.
  induction n as [|n IH]; cbn [completed].
  - split; [contradiction|lia].
  - rewrite in_app_iff, IH, in_at_candidate.
    split.
    + intros [[Hm Hj]|[-> Hj]]; auto with arith.
    + intros [Hm Hj]. destruct (Nat.eq_dec m n) as [->|Hne];
        [right; auto|left; split; [lia|exact Hj]].
Qed.

Lemma NoDup_map_injective {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x=y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinj Hnd. induction Hnd; cbn; constructor; auto.
  intro Hbad. apply in_map_iff in Hbad. destruct Hbad as [y [E Hy]].
  apply Hinj in E. subst. contradiction.
Qed.

Lemma NoDup_app_disjoint {A} (xs ys : list A) :
  NoDup xs -> NoDup ys ->
  (forall x, In x xs -> ~ In x ys) -> NoDup (xs++ys).
Proof.
  intros Hx Hy. induction Hx; cbn; intro Hd; auto.
  constructor.
  - rewrite in_app_iff. intros [Hbad|Hbad]; [contradiction|].
    exact (Hd x (or_introl eq_refl) Hbad).
  - apply IHHx. intros z Hz. apply Hd. right. exact Hz.
Qed.

Lemma NoDup_at_candidate n len : NoDup (at_candidate n len).
Proof.
  apply NoDup_map_injective; [intros x y E; now injection E|apply seq_NoDup].
Qed.

Lemma NoDup_completed n : NoDup (completed n).
Proof.
  induction n as [|n IH]; cbn [completed]; [constructor|].
  apply NoDup_app_disjoint; [exact IH|apply NoDup_at_candidate|].
  intros [m j] Hx Hy. apply in_completed in Hx.
  apply in_at_candidate in Hy. lia.
Qed.

Definition prefix n j := completed n ++ at_candidate n j.

Definition before_cut n j (x : occurrence) :=
  fst x < n \/ (fst x = n /\ snd x < j).

Lemma in_prefix n j m i :
  In (m,i) (prefix n j) <->
  (m<n /\ i<length (word m)) \/ (m=n /\ i<j).
Proof. unfold prefix. rewrite in_app_iff, in_completed, in_at_candidate. reflexivity. Qed.

Lemma NoDup_prefix n j : NoDup (prefix n j).
Proof.
  unfold prefix. apply NoDup_app_disjoint;
    [apply NoDup_completed|apply NoDup_at_candidate|].
  intros [m i] Hx Hy. apply in_completed in Hx.
  apply in_at_candidate in Hy. lia.
Qed.

Definition is_pop x :=
  match nth_error (word (fst x)) (snd x) with Some Nip => true | _ => false end.
Definition is_push x :=
  match nth_error (word (fst x)) (snd x) with Some Drop => true | _ => false end.

Lemma is_pop_spec x : is_pop x = true <-> Pop x.
Proof.
  unfold is_pop, Pop. destruct (nth_error _ _) as [k|];
    [destruct k|]; cbn; split; intros; congruence.
Qed.

Lemma is_push_spec x : is_push x = true <-> Push x.
Proof.
  unfold is_push, Push. destruct (nth_error _ _) as [k|];
    [destruct k|]; cbn; split; intros; congruence.
Qed.

Definition pops n j := filter is_pop (prefix n j).
Definition pushes n j := filter is_push (prefix n j).

Lemma in_pops n j x : In x (pops n j) <-> In x (prefix n j) /\ Pop x.
Proof. unfold pops. rewrite filter_In, is_pop_spec. reflexivity. Qed.
Lemma in_pushes n j x : In x (pushes n j) <-> In x (prefix n j) /\ Push x.
Proof. unfold pushes. rewrite filter_In, is_push_spec. reflexivity. Qed.

Lemma image_precedes n j x : fst x <= n -> Pop x -> In (lower x) (pushes n j).
Proof.
  intros Hn Hpop. apply in_pushes. split; [|now apply lower_push].
  pose proof (lower_earlier x Hpop) as Hlt.
  pose proof (lower_push x Hpop) as Hpush.
  destruct (lower x) as [m i] eqn:E. apply in_prefix. left.
  split; [cbn in Hlt; lia|].
  change (nth_error (word m) i = Some Drop) in Hpush.
  apply nth_error_Some. congruence.
Qed.

Lemma NoDup_lower xs : NoDup xs ->
  (forall x, In x xs -> Pop x) -> NoDup (map lower xs).
Proof.
  intros Hnd. induction Hnd as [|x xs Hfresh Hnd IH]; intro Hp;
    cbn; constructor.
  - intro H. apply in_map_iff in H. destruct H as [y [E Hy]].
    assert (y=x) by (apply lower_injective; [apply Hp; now right|apply Hp; now left|exact E]).
    subst. contradiction.
  - apply IH. intros y Hy. apply Hp. now right.
Qed.

Lemma concrete_finite_credit xs ys : NoDup xs ->
  (forall x, In x xs -> Pop x) ->
  (forall x, In x xs -> In (lower x) ys) -> length xs <= length ys.
Proof.
  intros Hnd Hp Hi. rewrite <- (map_length lower xs).
  apply NoDup_incl_length; [now apply NoDup_lower|].
  intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [<- Hx]].
  now apply Hi.
Qed.

(* Complete literal scheduler statement: no codec, injection, arithmetic,
   enumeration, or distinctness hypotheses remain. *)
Theorem every_prefix_has_credit n j : length (pops n j) <= length (pushes n j).
Proof.
  apply concrete_finite_credit.
  - apply NoDup_filter, NoDup_prefix.
  - intros x Hx. apply in_pops in Hx. tauto.
  - intros [m i] Hx. apply in_pops in Hx as [Hpre Hpop].
    apply image_precedes; [|exact Hpop].
    apply in_prefix in Hpre. cbn. lia.
Qed.

Theorem credit_before_each_pop n j : Pop (n,j) ->
  S (length (pops n j)) <= length (pushes n j).
Proof.
  intro Hpop. change (length ((n,j)::pops n j) <= length (pushes n j)).
  apply concrete_finite_credit.
  - constructor.
    + intro H. apply in_pops in H as [Hpre _]. apply in_prefix in Hpre. lia.
    + apply NoDup_filter, NoDup_prefix.
  - intros x [<-|Hx]; [exact Hpop|]. apply in_pops in Hx. tauto.
  - intros x [<-|Hx]; [apply image_precedes; [cbn; lia|exact Hpop]|].
    apply in_pops in Hx as [Hpre Hp]. apply image_precedes; [|exact Hp].
    destruct x as [m i]. apply in_prefix in Hpre. cbn. lia.
Qed.

(* An execution invariant with any additional nonnegative AX/MP credit
   immediately gives an available explicit head, above an opaque tail. *)
Corollary protected_head_available n j height : Pop (n,j) ->
  length (pushes n j) <= height + length (pops n j) -> 0 < height.
Proof. intros Hpop Hheight. pose proof (credit_before_each_pop n j Hpop). lia. Qed.

Example raw_zero_is_a_command : word 0 = [Drop].
Proof. reflexivity. Qed.
Example first_pop : word 1 = [Nip].
Proof. reflexivity. Qed.
Example final_zero_tag_is_not_empty : word 2 = [Drop;Drop].
Proof. reflexivity. Qed.
Example first_mp : word 3 = [Mp 0].
Proof. reflexivity. Qed.
Example nested_pop : word 4 = [Nip;Drop].
Proof. reflexivity. Qed.

Print Assumptions code_word.
Print Assumptions word_raw.
Print Assumptions lower_injective.
Print Assumptions every_prefix_has_credit.
Print Assumptions credit_before_each_pop.
Print Assumptions protected_head_available.

End ConcretePrefixCredit.
