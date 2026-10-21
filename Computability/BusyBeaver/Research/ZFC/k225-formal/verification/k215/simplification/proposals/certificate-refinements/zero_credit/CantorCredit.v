(* Concrete syntactic core for the ZC215 zero-credit scheduler.
   Original formalization, 2026-10-21.  Coq/Rocq standard library only.
   The final theorem concerns complete raw-code prefixes.  It does not
   assert that a physical Turing table implements that scheduler. *)
From Coq Require Import Arith.Cantor Lists.List Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

Definition pair (x y : nat) := Cantor.to_nat (x,y).
Lemma pair_inj x y x' y' : pair x y = pair x' y' -> x=x' /\ y=y'.
Proof. intro H. unfold pair in H. apply Cantor.to_nat_inj in H. inversion H. auto. Qed.
Lemma pair_right_le x y : y <= pair x y.
Proof. pose proof (Cantor.to_nat_non_decreasing x y). unfold pair. lia. Qed.
Lemma pair_right_strict x y z : y < z -> pair x y < pair x z.
Proof.
  intro H. pose proof (Cantor.to_nat_spec x y).
  pose proof (Cantor.to_nat_spec x z). unfold pair. nia.
Qed.
Lemma pair_tag_lower r : pair 0 r < pair 1 r.
Proof.
  pose proof (Cantor.to_nat_spec 0 r).
  pose proof (Cantor.to_nat_spec 1 r). unfold pair. nia.
Qed.

Inductive command : Type :=
| DROP | NIP | MP (x : nat) | AX (c x y : nat).
Definition emit (k : command) (r : nat) : nat :=
  match k with
  | DROP => pair 0 r
  | NIP => pair 1 r
  | MP x => pair 2 (pair x r)
  | AX c x y => pair (c+3) (pair y (pair x r))
  end.
Lemma emit_residual_le k r : r <= emit k r.
Proof.
  destruct k; simpl; repeat match goal with
  | |- _ <= pair ?a ?b => eapply Nat.le_trans; [|apply (pair_right_le a b)]
  end; lia.
Qed.
Lemma emit_strict k r s : r < s -> emit k r < emit k s.
Proof. destruct k; simpl; intro H; repeat apply pair_right_strict; exact H. Qed.
Lemma emit_inj k r k' r' : emit k r = emit k' r' -> k=k' /\ r=r'.
Proof.
  destruct k, k'; simpl; intro H; apply pair_inj in H;
  destruct H as [Htag Hrest]; try lia.
  - auto.
  - auto.
  - apply pair_inj in Hrest. destruct Hrest; subst; auto.
  - apply pair_inj in Hrest. destruct Hrest as [Hy Hrest].
    apply pair_inj in Hrest. destruct Hrest as [Hx Hr].
    assert (c=c0) by lia. subst; auto.
Qed.
Lemma emit_surjective n : exists k r, n=emit k r.
Proof.
  pose proof (Cantor.cancel_to_of n) as H.
  destruct (Cantor.of_nat n) as [t r] eqn:E.
  change (pair t r=n) in H. symmetry in H.
  destruct t as [|[|[|c]]].
  - exists DROP,r. exact H.
  - exists NIP,r. exact H.
  - pose proof (Cantor.cancel_to_of r) as Hr.
    destruct (Cantor.of_nat r) as [x s].
    exists (MP x),s. simpl. change (pair x s=r) in Hr. congruence.
  - pose proof (Cantor.cancel_to_of r) as Hr.
    destruct (Cantor.of_nat r) as [y q].
    pose proof (Cantor.cancel_to_of q) as Hq.
    destruct (Cantor.of_nat q) as [x s].
    exists (AX c x y),s. simpl.
    change (pair y q=r) in Hr. change (pair x s=q) in Hq.
    replace (c+3) with (S (S (S c))) by lia. congruence.
Qed.

(* Every word is nonempty. A terminal DROP has raw code zero. *)
Inductive word : Type := last (k : command) | more (k : command) (w : word).
Fixpoint encode (w : word) : nat :=
  match w with last k => emit k 0 | more k v => emit k (S (encode v)) end.
Fixpoint word_length (w : word) : nat :=
  match w with last _ => 1 | more _ v => S(word_length v) end.
Fixpoint nth_command (w : word) (j : nat) : option command :=
  match w,j with
  | last k,0 | more k _,0 => Some k
  | last _,S _ => None
  | more _ v,S i => nth_command v i
  end.
Fixpoint set_command (w : word) (j : nat) (k : command) : word :=
  match w,j with
  | last _,0 => last k
  | more _ v,0 => more k v
  | last c,S _ => last c
  | more c v,S i => more c (set_command v i k)
  end.
Theorem encode_injective w v : encode w=encode v -> w=v.
Proof.
  revert v. induction w as [k|k w IH]; intros [k'|k' v]; simpl; intro H;
  apply emit_inj in H; destruct H as [Hk Hr]; subst; try discriminate; auto.
  f_equal. apply IH. lia.
Qed.
Theorem every_raw_code n : exists w, encode w=n.
Proof.
  induction n using lt_wf_ind.
  destruct (emit_surjective n) as [k [r E]].
  destruct r as [|r].
  - exists (last k). simpl. auto.
  - assert (r<n) as Hr.
    { pose proof (emit_residual_le k (S r)). lia. }
    destruct (H r Hr) as [w Hw].
    exists (more k w). simpl. congruence.
Qed.
Theorem unique_raw_word n : exists! w, encode w=n.
Proof.
  destruct (every_raw_code n) as [w Hw]. exists w. split; [exact Hw|].
  intros v Hv. apply encode_injective. congruence.
Qed.
Lemma at_bound w j k : nth_command w j=Some k -> j<word_length w.
Proof.
  revert j. induction w; intros [|j]; simpl; try discriminate; try lia.
  intro H. specialize (IHw j H). lia.
Qed.
Lemma replace_at w j a b : nth_command w j=Some a -> nth_command (set_command w j b) j=Some b.
Proof. revert j. induction w; intros [|j]; simpl; try discriminate; auto. Qed.
Lemma replace_restore w j a b : nth_command w j=Some a -> set_command (set_command w j b) j a=w.
Proof.
  revert j. induction w; intros [|j]; simpl; try discriminate.
  - intros H. inversion H. reflexivity.
  - intros H. inversion H. reflexivity.
  - intro H. f_equal. apply IHw. exact H.
Qed.
Lemma replace_length w j b : word_length (set_command w j b)=word_length w.
Proof. revert j. induction w; intros [|j]; simpl; auto. Qed.
Theorem concrete_tag_lowering w j :
  nth_command w j=Some NIP -> encode (set_command w j DROP)<encode w.
Proof.
  revert j. induction w as [k|k w IH]; intros [|j]; simpl; try discriminate.
  - intros H. inversion H. apply pair_tag_lower.
  - intros H. inversion H. apply pair_tag_lower.
  - intro H. apply emit_strict. specialize (IH j H). lia.
Qed.

Definition occurrence := (word * nat)%type.
Definition is_pop (x : occurrence) : bool :=
  match nth_command (fst x) (snd x) with Some NIP => true | _ => false end.
Definition is_push (x : occurrence) : bool :=
  match nth_command (fst x) (snd x) with Some DROP => true | _ => false end.
Definition lower (x : occurrence) : occurrence :=
  (set_command (fst x) (snd x) DROP,snd x).
Definition raise (x : occurrence) : occurrence :=
  (set_command (fst x) (snd x) NIP,snd x).
Lemma pop_spec x : is_pop x=true <-> nth_command (fst x) (snd x)=Some NIP.
Proof.
  unfold is_pop. destruct (nth_command (fst x) (snd x)) as [k|];
  [destruct k|]; split; intro H; try discriminate; reflexivity.
Qed.
Lemma push_spec x : is_push x=true <-> nth_command (fst x) (snd x)=Some DROP.
Proof.
  unfold is_push. destruct (nth_command (fst x) (snd x)) as [k|];
  [destruct k|]; split; intro H; try discriminate; reflexivity.
Qed.
Lemma lower_is_push x : is_pop x=true -> is_push (lower x)=true.
Proof.
  rewrite pop_spec, push_spec. destruct x as [w j]. simpl. apply replace_at.
Qed.
Lemma raise_lower x : is_pop x=true -> raise (lower x)=x.
Proof.
  rewrite pop_spec. destruct x as [w j]. unfold raise,lower. simpl.
  intro H. rewrite (replace_restore w j NIP DROP H). reflexivity.
Qed.
Theorem lower_injective x y :
  is_pop x=true -> is_pop y=true -> lower x=lower y -> x=y.
Proof.
  intros Hx Hy E. apply (f_equal raise) in E.
  rewrite (raise_lower x Hx),(raise_lower y Hy) in E. exact E.
Qed.
Theorem lower_rank x : is_pop x=true -> encode(fst(lower x))<encode(fst x).
Proof. rewrite pop_spec. destruct x as [w j]. apply concrete_tag_lowering. Qed.

(* A complete raw prefix includes every occurrence of each earlier raw
   candidate. The current candidate itself may be cut at any position. *)
Definition raw_prefix (xs : list occurrence) : Prop :=
  forall w j, In (w,j) xs ->
  forall v i, encode v<encode w -> i<word_length v -> In (v,i) xs.
Lemma NoDup_map_on {A B : Type} (f:A->B) xs :
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x=f y -> x=y) ->
  NoDup (map f xs).
Proof.
  intro H. induction H as [|x xs Hfresh Hnd IH]; intro Hinj; simpl.
  - constructor.
  - constructor.
    + intro Hmap. apply in_map_iff in Hmap. destruct Hmap as [y [E Hy]].
      assert (x=y) by (apply Hinj; simpl; auto). subst. contradiction.
    + apply IH. intros a b Ha Hb E. apply Hinj; simpl; auto.
Qed.
Theorem concrete_prefix_credit xs :
  NoDup xs -> raw_prefix xs ->
  length (filter is_pop xs) <= length (filter is_push xs).
Proof.
  intros Hnd Hprefix.
  assert (Hmap : NoDup (map lower (filter is_pop xs))).
  { apply NoDup_map_on.
    - apply NoDup_filter. exact Hnd.
    - intros x y Hx Hy E.
      apply filter_In in Hx. apply filter_In in Hy.
      apply lower_injective; tauto. }
  assert (Hincl : incl (map lower (filter is_pop xs)) (filter is_push xs)).
  { intros z Hz. apply in_map_iff in Hz. destruct Hz as [x [E Hx]]. subst z.
    apply filter_In in Hx. destruct Hx as [Hin Hpop].
    apply filter_In. split; [|apply lower_is_push; exact Hpop].
    destruct x as [w j]. apply pop_spec in Hpop. simpl in Hpop.
    unfold lower. simpl. apply (Hprefix w j Hin).
    - apply concrete_tag_lowering. exact Hpop.
    - rewrite replace_length. eapply at_bound. exact Hpop. }
  pose proof (NoDup_incl_length Hmap Hincl) as Hlen.
  rewrite map_length in Hlen. exact Hlen.
Qed.
Theorem credit_before_next_pop xs x :
  NoDup (x::xs) -> raw_prefix (x::xs) -> is_pop x=true ->
  length (filter is_pop xs) < length (filter is_push xs).
Proof.
  intros Hnd Hprefix Hpop.
  pose proof (concrete_prefix_credit (x::xs) Hnd Hprefix) as H.
  simpl in H. rewrite Hpop in H.
  assert (is_push x=false) as Hpush.
  { apply pop_spec in Hpop. unfold is_push. rewrite Hpop. reflexivity. }
  rewrite Hpush in H. simpl in H. lia.
Qed.

Print Assumptions unique_raw_word.
Print Assumptions concrete_tag_lowering.
Print Assumptions lower_injective.
Print Assumptions concrete_prefix_credit.
Print Assumptions credit_before_next_pop.

(* Executable raw decoder, with fuel justified by the actual residual
   descent. This closes the abstract parsing hypotheses used in earlier
   PrefixCredit.v proposals. No choice or excluded middle is used. *)
Definition split_command n : command * nat :=
  let '(t,r) := Cantor.of_nat n in
  match t with
  | 0 => (DROP,r)
  | 1 => (NIP,r)
  | 2 => let '(x,s) := Cantor.of_nat r in (MP x,s)
  | S (S (S c)) =>
      let '(y,q) := Cantor.of_nat r in
      let '(x,s) := Cantor.of_nat q in (AX c x y,s)
  end.
Lemma split_command_spec n : n=emit (fst(split_command n)) (snd(split_command n)).
Proof.
  unfold split_command.
  pose proof (Cantor.cancel_to_of n) as H.
  destruct (Cantor.of_nat n) as [t r]. change (pair t r=n) in H.
  destruct t as [|[|[|c]]]; simpl.
  - auto.
  - auto.
  - pose proof (Cantor.cancel_to_of r) as Hr.
    destruct (Cantor.of_nat r) as [x s]. simpl.
    change (pair x s=r) in Hr. congruence.
  - pose proof (Cantor.cancel_to_of r) as Hr.
    destruct (Cantor.of_nat r) as [y q].
    pose proof (Cantor.cancel_to_of q) as Hq.
    destruct (Cantor.of_nat q) as [x s]. simpl.
    change (pair y q=r) in Hr. change (pair x s=q) in Hq.
    replace (c+3) with (S(S(S c))) by lia. congruence.
Qed.
Fixpoint decode_fuel fuel n : word :=
  match fuel with
  | 0 => last DROP
  | S fuel => let '(k,r) := split_command n in
      match r with 0 => last k | S m => more k (decode_fuel fuel m) end
  end.
Definition decode n := decode_fuel (S n) n.
Lemma decode_fuel_correct fuel n : n<fuel -> encode(decode_fuel fuel n)=n.
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Hlt; [lia|].
  simpl. pose proof (split_command_spec n) as E.
  destruct (split_command n) as [k r]. simpl in E.
  destruct r as [|r]; simpl; [auto|].
  assert (r<fuel) as Hr.
  { pose proof (emit_residual_le k (S r)). lia. }
  rewrite (IH r Hr). auto.
Qed.
Theorem encode_decode n : encode(decode n)=n.
Proof. apply decode_fuel_correct. lia. Qed.
Theorem decode_encode w : decode(encode w)=w.
Proof. apply encode_injective. apply encode_decode. Qed.

Definition positions (w : word) (m : nat) : list occurrence :=
  map (fun j => (w,j)) (seq 0 m).
Fixpoint completed n : list occurrence :=
  match n with
  | 0 => []
  | S m => completed m ++ positions (decode m) (word_length(decode m))
  end.
Definition schedule_cut n j := completed n ++ positions (decode n) j.

Lemma positions_spec w m v j :
  In (v,j) (positions w m) <-> v=w /\ j<m.
Proof.
  unfold positions. rewrite in_map_iff. split.
  - intros [i [E Hi]]. inversion E; subst. apply in_seq in Hi. split; [reflexivity|lia].
  - intros [E H]. subst v. exists j. split; [reflexivity|].
    apply in_seq. lia.
Qed.
Lemma completed_spec n w j :
  In (w,j) (completed n) <-> encode w<n /\ j<word_length w.
Proof.
  induction n as [|n IH]; simpl.
  - split; [contradiction|lia].
  - rewrite in_app_iff,IH,positions_spec. split.
    + intros [[H1 H2]|[E Hj]]; [lia|].
      subst w. rewrite encode_decode. lia.
    + intros [Hn Hj]. destruct (Nat.lt_ge_cases (encode w) n) as [H|H].
      * left. auto.
      * right. assert (encode w=n) as E by lia.
        assert (w=decode n) as Ew by (apply encode_injective; rewrite encode_decode; exact E).
        split; [exact Ew|]. rewrite <- Ew. exact Hj.
Qed.
Lemma NoDup_app_disjoint {A:Type} (xs ys:list A) :
  NoDup xs -> NoDup ys ->
  (forall x, In x xs -> ~In x ys) -> NoDup(xs++ys).
Proof.
  intro H. induction H as [|x xs Hx Hnd IH]; intros Hy Hd; simpl; [exact Hy|].
  constructor.
  - rewrite in_app_iff. intros [Hin|Hin]; [contradiction|].
    apply (Hd x); simpl; auto.
  - apply IH; [exact Hy|]. intros a Ha. apply Hd. simpl. auto.
Qed.
Lemma positions_nodup w m : NoDup(positions w m).
Proof.
  unfold positions. apply NoDup_map_on.
  - apply seq_NoDup.
  - intros x y _ _ E. inversion E. reflexivity.
Qed.
Lemma completed_nodup n : NoDup(completed n).
Proof.
  induction n as [|n IH]; simpl; [constructor|].
  apply NoDup_app_disjoint; [exact IH|apply positions_nodup|].
  intros [w j] Hin Hlast. apply completed_spec in Hin.
  apply positions_spec in Hlast. destruct Hlast as [E _]. subst w.
  rewrite encode_decode in Hin. lia.
Qed.
Lemma schedule_cut_spec n j w i :
  In (w,i)(schedule_cut n j) <->
  (encode w<n /\ i<word_length w) \/ (w=decode n /\ i<j).
Proof. unfold schedule_cut. rewrite in_app_iff, completed_spec, positions_spec. reflexivity. Qed.
Lemma schedule_cut_nodup n j : NoDup(schedule_cut n j).
Proof.
  unfold schedule_cut. apply NoDup_app_disjoint.
  - apply completed_nodup.
  - apply positions_nodup.
  - intros [w i] Hin Hlast. apply completed_spec in Hin.
    apply positions_spec in Hlast. destruct Hlast as [E _]. subst w.
    rewrite encode_decode in Hin. lia.
Qed.
Lemma schedule_cut_raw_prefix n j : raw_prefix(schedule_cut n j).
Proof.
  intros w i Hin v k Hlt Hk. apply schedule_cut_spec in Hin.
  apply schedule_cut_spec. left. split; [|exact Hk].
  destruct Hin as [[Hn _]|[E _]]; [lia|].
  subst w. rewrite encode_decode in Hlt. exact Hlt.
Qed.

(* Closed, concrete theorem for every cut in W(0)W(1)W(2)... . *)
Theorem exhaustive_schedule_zero_credit n j :
  length(filter is_pop (schedule_cut n j)) <=
  length(filter is_push (schedule_cut n j)).
Proof.
  apply concrete_prefix_credit.
  - apply schedule_cut_nodup.
  - apply schedule_cut_raw_prefix.
Qed.
Print Assumptions encode_decode.
Print Assumptions decode_encode.
Print Assumptions exhaustive_schedule_zero_credit.

Lemma positions_succ w j : positions w (S j)=positions w j++[(w,j)].
Proof.
  unfold positions. rewrite seq_S,map_app. simpl. reflexivity.
Qed.
Lemma schedule_cut_succ n j :
  schedule_cut n (S j)=schedule_cut n j++[(decode n,j)].
Proof.
  unfold schedule_cut. rewrite positions_succ,app_assoc. reflexivity.
Qed.
Theorem exhaustive_credit_before_nip n j :
  nth_command (decode n) j=Some NIP ->
  length(filter is_pop (schedule_cut n j)) <
  length(filter is_push (schedule_cut n j)).
Proof.
  intro Hnip.
  pose proof (exhaustive_schedule_zero_credit n (S j)) as H.
  assert (Hp : is_pop (decode n,j)=true).
  { apply pop_spec. exact Hnip. }
  assert (Hq : is_push (decode n,j)=false).
  { unfold is_push. simpl. rewrite Hnip. reflexivity. }
  rewrite schedule_cut_succ, !filter_app, !app_length in H.
  change (length(filter is_pop (schedule_cut n j)) +
      length(if is_pop (decode n,j) then [(decode n,j)] else []) <=
    length(filter is_push (schedule_cut n j)) +
      length(if is_push (decode n,j) then [(decode n,j)] else [])) in H.
  rewrite Hp,Hq in H. simpl in H. lia.
Qed.

Example first_word : decode 0=last DROP.
Proof. reflexivity. Qed.
Example second_word : decode 1=last NIP.
Proof. reflexivity. Qed.
Example third_word : decode 2=more DROP (last DROP).
Proof. reflexivity. Qed.
Print Assumptions exhaustive_credit_before_nip.
