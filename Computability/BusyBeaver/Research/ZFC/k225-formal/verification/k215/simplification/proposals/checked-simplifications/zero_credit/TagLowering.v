(* Concrete ZC215 tag-lowering certificate.
   The tag-lowering idea and codec are inherited from ProveIt's ZC215
   proofs/tag_lowering_credit.md; this file supplies a new kernel-checked
   formalization. It is not an exact binary-machine correctness endpoint. *)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Fixpoint tri (n : nat) : nat :=
  match n with 0 => 0 | S k => tri k + S k end.
Definition cp (a b : nat) : nat := tri (a+b) + b.
Lemma tri_double n : 2 * tri n = n * (n+1).
Proof. induction n; simpl in *; nia. Qed.
Lemma tri_closed n : tri n = n*(n+1)/2.
Proof.
  rewrite <- tri_double, Nat.mul_comm. symmetry. apply Nat.div_mul. discriminate.
Qed.
Lemma cp_closed a b : cp a b = (a+b)*(a+b+1)/2+b.
Proof. unfold cp. now rewrite tri_closed. Qed.

Lemma tri_mono a b : a <= b -> tri a <= tri b.
Proof. intro H. induction H; simpl; lia. Qed.
Lemma tri_gap a b : a < b -> tri a + a < tri b.
Proof.
  intro H. pose proof (tri_mono (S a) b H). simpl in H0. lia.
Qed.
Lemma cp_inj a b c d : cp a b = cp c d -> a=c /\ b=d.
Proof.
  unfold cp. intro E.
  assert (a+b=c+d).
  { destruct (Nat.lt_trichotomy (a+b) (c+d)) as [H|[H|H]].
    - pose proof (tri_gap _ _ H). lia.
    - exact H.
    - pose proof (tri_gap _ _ H). lia. }
  rewrite H in E. lia.
Qed.
Lemma cp_mono_right a b c : b < c -> cp a b < cp a c.
Proof.
  intro H. unfold cp. assert (a+b <= a+c) by lia.
  pose proof (tri_mono _ _ H0). lia.
Qed.
Lemma cp_lower r : cp 0 r < cp 1 r.
Proof. unfold cp. simpl. lia. Qed.
Lemma cp_second a b : b <= cp a b.
Proof. unfold cp; lia. Qed.

(* An executable inverse by walking the Cantor diagonals. *)
Fixpoint unc (n : nat) : nat * nat :=
  match n with
  | 0 => (0,0)
  | S k => let '(a,b) := unc k in
      match a with 0 => (S b,0) | S a' => (a',S b) end
  end.
Lemma cp_unc n : cp (fst (unc n)) (snd (unc n)) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. destruct (unc n) as [a b] eqn:E. simpl in IH.
  destruct a; simpl; unfold cp in *; simpl in *.
  - rewrite !Nat.add_0_r. lia.
  - replace (a+S b) with (S (a+b)) by lia. simpl. lia.
Qed.
Lemma unc_cp a b : unc (cp a b) = (a,b).
Proof.
  pose proof (cp_unc (cp a b)) as H.
  destruct (unc (cp a b)) as [c d]; simpl in H.
  apply cp_inj in H. destruct H; subst; reflexivity.
Qed.

Inductive Cmd : Type := DROP | NIP | MP (x:nat) | AX (c x y:nat).
Definition ec (c:Cmd) (r:nat) : nat :=
  match c with
  | DROP => cp 0 r
  | NIP => cp 1 r
  | MP x => cp 2 (cp x r)
  | AX t x y => cp (t+3) (cp y (cp x r))
  end.
Definition dc (n:nat) : Cmd * nat :=
  let '(t,r) := unc n in
  match t with
  | 0 => (DROP,r)
  | 1 => (NIP,r)
  | 2 => let '(x,s) := unc r in (MP x,s)
  | S (S (S t)) => let '(y,s) := unc r in
      let '(x,v) := unc s in (AX t x y,v)
  end.
Lemma ec_mono c r s : r < s -> ec c r < ec c s.
Proof. intro H. destruct c; simpl; repeat apply cp_mono_right; exact H. Qed.
Lemma ec_second c r : r <= ec c r.
Proof.
  destruct c; simpl.
  - apply cp_second.
  - apply cp_second.
  - eapply Nat.le_trans; [apply cp_second | apply cp_second].
  - eapply Nat.le_trans; [apply cp_second |].
    eapply Nat.le_trans; [apply cp_second | apply cp_second].
Qed.
Lemma ec_dc n : ec (fst (dc n)) (snd (dc n)) = n.
Proof.
  unfold dc. pose proof (cp_unc n) as H.
  destruct (unc n) as [t r] eqn:E; simpl in H.
  destruct t as [|[|[|t]]]; simpl; try exact H.
  - pose proof (cp_unc r) as H1.
    destruct (unc r) as [x s]; simpl in *. now rewrite H1.
  - pose proof (cp_unc r) as H1.
    destruct (unc r) as [y s]; simpl in H1.
    pose proof (cp_unc s) as H2.
    destruct (unc s) as [x v]; simpl in *.
    replace (t+3) with (S (S (S t))) by lia.
    now rewrite H2, H1.
Qed.
Lemma dc_ec c r : dc (ec c r) = (c,r).
Proof.
  destruct c; unfold ec, dc; rewrite unc_cp; simpl; try reflexivity.
  - now rewrite unc_cp.
  - replace (c+3) with (S(S(S c))) by lia. simpl.
    now rewrite !unc_cp.
Qed.
Lemma ec_inj c d r s : ec c r = ec d s -> c=d /\ r=s.
Proof.
  intro H. apply (f_equal dc) in H. rewrite !dc_ec in H.
  inversion H. auto.
Qed.

Fixpoint raw (w:list Cmd) : nat :=
  match w with
  | [] => 0
  | c::ws => ec c (match ws with []=>0 | _=>S (raw ws) end)
  end.
Lemma raw_inj w v : w<>[] -> v<>[] -> raw w=raw v -> w=v.
Proof.
  revert v. induction w as [|c w IH]; intros v Hw Hv E; [contradiction|].
  destruct v as [|d v]; [contradiction|]. simpl in E.
  apply ec_inj in E. destruct E as [Ec E]. subst d.
  f_equal. destruct w as [|a w], v as [|b v]; try reflexivity;
    try discriminate.
  apply IH; try discriminate. injection E; auto.
Qed.

(* Fuel only implements well-founded parsing; the sufficient fuel is n+1. *)
Fixpoint parse_fuel (fuel n:nat) : list Cmd :=
  match fuel with
  | 0 => []
  | S f => let '(c,r) := dc n in
      match r with 0=>[c] | S k => c :: parse_fuel f k end
  end.
Lemma parse_fuel_correct f n : n < f ->
  parse_fuel f n <> [] /\ raw (parse_fuel f n) = n.
Proof.
  revert n. induction f as [|f IH]; intros n Hnf; [lia|].
  simpl. pose proof (ec_dc n) as He.
  destruct (dc n) as [c r] eqn:E. simpl in He.
  pose proof (ec_second c r) as Hr. rewrite He in Hr.
  destruct r as [|k].
  - split; [discriminate|]. simpl. exact He.
  - assert (k<f) by lia. destruct (IH k H) as [Hne Heq].
    split; [discriminate|]. simpl.
    destruct (parse_fuel f k); [contradiction|]. rewrite Heq. exact He.
Qed.
Definition parse n := parse_fuel (S n) n.
Lemma parse_nonempty n : parse n <> [].
Proof. apply (proj1 (parse_fuel_correct (S n) n (Nat.lt_succ_diag_r n))). Qed.
Lemma raw_parse n : raw (parse n) = n.
Proof. apply (proj2 (parse_fuel_correct (S n) n (Nat.lt_succ_diag_r n))). Qed.
Lemma parse_raw w : w<>[] -> parse (raw w)=w.
Proof.
  intro H. apply raw_inj; [apply parse_nonempty|exact H|apply raw_parse].
Qed.

Fixpoint replace_at (j:nat) (c:Cmd) (w:list Cmd) : list Cmd :=
  match j,w with
  | _,[] => []
  | 0,_::ws => c::ws
  | S k,d::ws => d::replace_at k c ws
  end.
Inductive Lower : nat -> list Cmd -> list Cmd -> Prop :=
| lower_here : forall ws, Lower 0 (NIP::ws) (DROP::ws)
| lower_there : forall j w v c, Lower j w v -> Lower (S j) (c::w) (c::v).
Lemma lower_of_nth j w : nth_error w j=Some NIP ->
  Lower j w (replace_at j DROP w).
Proof.
  revert w. induction j; intros [|c w] H; try discriminate; simpl in *.
  - inversion H. constructor.
  - constructor. auto.
Qed.
Lemma lower_nonempty j w v : Lower j w v -> w<>[] /\ v<>[].
Proof. intro H. inversion H; split; discriminate. Qed.
Lemma lower_nth j w v : Lower j w v -> nth_error v j=Some DROP.
Proof. intro H. induction H; simpl; auto. Qed.
Lemma lower_smaller j w v : Lower j w v -> raw v < raw w.
Proof.
  intro H. induction H.
  - simpl. apply cp_lower.
  - destruct (lower_nonempty _ _ _ H) as [Hw Hv].
    destruct w, v; try contradiction. simpl in *.
    apply ec_mono. lia.
Qed.
Lemma lower_inverse j w v : Lower j w v ->
  forall w', Lower j w' v -> w=w'.
Proof.
  intro H. induction H; intros w' H'; inversion H'; subst; auto.
  f_equal. eauto.
Qed.

Definition Occ := (nat*nat)%type.
Definition Pop (o:Occ) := nth_error (parse (fst o)) (snd o)=Some NIP.
Definition Push (o:Occ) := nth_error (parse (fst o)) (snd o)=Some DROP.
Definition lower (o:Occ) : Occ :=
  (raw (replace_at (snd o) DROP (parse (fst o))), snd o).
Lemma lower_push o : Pop o -> Push (lower o).
Proof.
  destruct o as [n j]; unfold Pop, Push, lower; simpl. intro H.
  pose proof (lower_of_nth j (parse n) H) as L.
  destruct (lower_nonempty _ _ _ L) as [_ Hne].
  rewrite parse_raw by exact Hne. now apply lower_nth in L.
Qed.
Lemma lower_earlier o : Pop o -> fst (lower o) < fst o.
Proof.
  destruct o as [n j]; unfold Pop, lower; simpl. intro H.
  pose proof (lower_smaller _ _ _ (lower_of_nth j (parse n) H)).
  now rewrite raw_parse in H0.
Qed.
Lemma lower_injective x y : Pop x -> Pop y -> lower x=lower y -> x=y.
Proof.
  destruct x as [n j], y as [m k]. unfold Pop, lower; simpl.
  intros Hn Hm E. injection E as Er Ek. subst k.
  pose proof (lower_of_nth j (parse n) Hn) as Ln.
  pose proof (lower_of_nth j (parse m) Hm) as Lm.
  assert (replace_at j DROP (parse n)=replace_at j DROP (parse m)) as Ev.
  { apply raw_inj; try exact Er; apply lower_nonempty in Ln, Lm; tauto. }
  rewrite <- Ev in Lm.
  pose proof (lower_inverse _ _ _ Ln _ Lm) as Ep.
  apply (f_equal raw) in Ep. rewrite !raw_parse in Ep. subst m. reflexivity.
Qed.

Print Assumptions lower_injective.
Print Assumptions lower_earlier.
Print Assumptions parse_raw.

(* Finite injection counting, adapted from the uncompiled PrefixCredit.v
   prototype in the GC-ZC215 incoming packet. *)
Lemma nodup_map_on {A B:Type} (f:A->B) xs :
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x=f y -> x=y) ->
  NoDup (map f xs).
Proof.
  intros H. induction H as [|x xs Hfresh Hnd IH]; intro Hinj.
  - constructor.
  - simpl. constructor.
    + intro H. apply in_map_iff in H. destruct H as [y [E Hy]].
      assert (y=x) by (apply Hinj; simpl; auto). subst; contradiction.
    + apply IH. intros a b Ha Hb E. apply Hinj; simpl; auto.
Qed.
Lemma injection_count {A B:Type} (f:A->B) xs ys :
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x=f y -> x=y) ->
  (forall x, In x xs -> In (f x) ys) -> length xs <= length ys.
Proof.
  intros Hn Hi Hc.
  assert (Hmap:NoDup (map f xs)) by (apply nodup_map_on; assumption).
  assert (Hin:incl (map f xs) ys).
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [E Hx]].
    subst. auto. }
  pose proof (NoDup_incl_length Hmap Hin) as Hlen.
  now rewrite map_length in Hlen.
Qed.
Lemma nodup_append {A:Type} (xs ys:list A) :
  NoDup xs -> NoDup ys ->
  (forall x, In x xs -> ~ In x ys) -> NoDup (xs++ys).
Proof.
  intros Hx Hy. induction Hx as [|a xs Ha Hx IH]; intro Hd; simpl; auto.
  constructor.
  - rewrite in_app_iff. intros [H|H]; [contradiction|]. apply (Hd a); simpl; auto.
  - apply IH. intros x Hx'. apply Hd. simpl; auto.
Qed.

Definition row n j : list Occ := map (fun k => (n,k)) (seq 0 j).
Lemma in_row n j (x:Occ) : In x (row n j) <-> fst x=n /\ snd x<j.
Proof.
  destruct x as [m k]; unfold row; simpl. rewrite in_map_iff.
  split.
  - intros [t [E H]]. inversion E; subst. rewrite in_seq in H. lia.
  - intros [E H]. subst m. exists k. split; [reflexivity|].
    rewrite in_seq. lia.
Qed.
Lemma nodup_row n j : NoDup (row n j).
Proof.
  unfold row. apply nodup_map_on; [apply seq_NoDup|].
  intros x y _ _ E. now inversion E.
Qed.
Fixpoint complete (n:nat) : list Occ :=
  match n with
  | 0 => []
  | S k => complete k ++ row k (length (parse k))
  end.
Lemma in_complete n x : In x (complete n) <->
  fst x<n /\ snd x<length (parse (fst x)).
Proof.
  induction n as [|n IH]; simpl.
  - split; [tauto|lia].
  - rewrite in_app_iff, IH, in_row. split.
    + intros [[H H']|[E H']]; [lia|]. rewrite E. auto with arith.
    + intros [H H']. destruct (Nat.eq_dec (fst x) n) as [E|E].
      * right. rewrite <- E. auto.
      * left. lia.
Qed.
Lemma nodup_complete n : NoDup (complete n).
Proof.
  induction n; simpl; [constructor|].
  apply nodup_append; [exact IHn|apply nodup_row|].
  intros x Hc Hr. apply in_complete in Hc. apply in_row in Hr. lia.
Qed.
Definition prefix n j := complete n ++ row n j.
Lemma nodup_prefix n j : NoDup (prefix n j).
Proof.
  apply nodup_append; [apply nodup_complete|apply nodup_row|].
  intros x Hc Hr. apply in_complete in Hc. apply in_row in Hr. lia.
Qed.
Lemma in_prefix n j x : In x (prefix n j) <->
  (fst x<n /\ snd x<length (parse (fst x))) \/
  (fst x=n /\ snd x<j).
Proof. unfold prefix. now rewrite in_app_iff, in_complete, in_row. Qed.
Lemma push_valid x : Push x -> snd x < length (parse (fst x)).
Proof.
  unfold Push. intro H. apply nth_error_Some. rewrite H. discriminate.
Qed.
Lemma lower_in_prefix n j x : In x (prefix n j) -> Pop x ->
  In (lower x) (prefix n j).
Proof.
  intros Hx Hp. apply in_prefix in Hx. apply in_prefix. left.
  pose proof (lower_earlier x Hp). split; [lia|].
  apply push_valid. now apply lower_push.
Qed.
Lemma imminent_lower_in_prefix n j : Pop (n,j) ->
  In (lower (n,j)) (prefix n j).
Proof.
  intro Hp. apply in_prefix. left. split.
  - exact (lower_earlier (n,j) Hp).
  - apply push_valid. now apply lower_push.
Qed.

Definition popb o :=
  match nth_error (parse (fst o)) (snd o) with Some NIP=>true | _=>false end.
Definition pushb o :=
  match nth_error (parse (fst o)) (snd o) with Some DROP=>true | _=>false end.
Lemma popb_spec o : popb o=true <-> Pop o.
Proof.
  unfold popb, Pop. destruct (nth_error (parse (fst o)) (snd o)) as [c|];
    [destruct c|]; split; intro H; try discriminate; reflexivity.
Qed.
Lemma pushb_spec o : pushb o=true <-> Push o.
Proof.
  unfold pushb, Push. destruct (nth_error (parse (fst o)) (snd o)) as [c|];
    [destruct c|]; split; intro H; try discriminate; reflexivity.
Qed.
Definition pops n j := filter popb (prefix n j).
Definition pushes n j := filter pushb (prefix n j).
Lemma in_pops n j o : In o (pops n j) <-> In o (prefix n j) /\ Pop o.
Proof. unfold pops. now rewrite filter_In, popb_spec. Qed.
Lemma in_pushes n j o : In o (pushes n j) <-> In o (prefix n j) /\ Push o.
Proof. unfold pushes. now rewrite filter_In, pushb_spec. Qed.

(* No assumptions about AX's contribution, theoremhood, or startup credit. *)
Theorem zero_credit n j : length (pops n j) <= length (pushes n j).
Proof.
  apply (injection_count lower).
  - apply NoDup_filter. apply nodup_prefix.
  - intros x y Hx Hy E. apply in_pops in Hx, Hy.
    apply lower_injective; tauto.
  - intros x Hx. apply in_pops in Hx. apply in_pushes. split.
    + apply lower_in_prefix; tauto.
    + apply lower_push; tauto.
Qed.
Theorem positive_credit_before_nip n j : Pop (n,j) ->
  S (length (pops n j)) <= length (pushes n j).
Proof.
  intro Hp. change (length ((n,j)::pops n j) <= length (pushes n j)).
  apply (injection_count lower).
  - constructor.
    + intro H. apply in_pops in H. destruct H as [H _].
      apply in_prefix in H. simpl in H. lia.
    + apply NoDup_filter. apply nodup_prefix.
  - intros x y Hx Hy E. simpl in Hx, Hy.
    assert (Pop x) as Hpx by (destruct Hx as [<-|H]; [exact Hp|apply in_pops in H; tauto]).
    assert (Pop y) as Hpy by (destruct Hy as [<-|H]; [exact Hp|apply in_pops in H; tauto]).
    now apply lower_injective.
  - intros x Hx. simpl in Hx. destruct Hx as [<-|H].
    + apply in_pushes. split; [now apply imminent_lower_in_prefix|now apply lower_push].
    + apply in_pops in H. apply in_pushes. split.
      * apply lower_in_prefix; tauto.
      * apply lower_push; tauto.
Qed.

Print Assumptions zero_credit.
Print Assumptions positive_credit_before_nip.
