From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith Lia.
From K215F Require Import TM230.
Require Import NativeContext.
Import ListNotations.
Module N := NativeContext.
Module S := K215F.TM230.TM230.

Definition relabel (q : nat) : nat :=
  if Nat.eqb q 301 then 102 else
  if Nat.eqb q 302 then 120 else
  if Nat.eqb q 254 then 230 else q.
Definition old_labels : list nat := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159; 160; 161; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 176; 177; 178; 179; 180; 181; 182; 184; 185; 186; 187; 188; 189; 190; 193; 194; 195; 196; 197; 198; 199; 200; 201; 203; 204; 205; 206; 207; 209; 210; 211; 212; 213; 214; 215; 216; 217; 218; 220; 221; 222; 223; 225; 254; 301; 302].
Definition active (q : nat) := existsb (Nat.eqb q) old_labels = true.
Definition direction (d : N.dir) : BusyCoq.TM.dir :=
  match d with N.L => BusyCoq.TM.L | N.R => BusyCoq.TM.R end.
Definition image (x : option N.action) : option (bool * BusyCoq.TM.dir * nat) :=
  match x with None => None | Some (N.A w d z) => Some (w, direction d, relabel z) end.

Lemma active_in q : active q -> In q old_labels.
Proof.
  unfold active. rewrite existsb_exists.
  intros (x & Hx & E). apply Nat.eqb_eq in E. subst. exact Hx.
Qed.

Definition direction_eqb (d e : BusyCoq.TM.dir) :=
  match d,e with BusyCoq.TM.L,BusyCoq.TM.L | BusyCoq.TM.R,BusyCoq.TM.R => true | _,_ => false end.
Definition image_eqb (x y : option (bool * BusyCoq.TM.dir * nat)) :=
  match x,y with
  | None,None => true
  | Some (w,d,q),Some (v,e,r) => Bool.eqb w v && direction_eqb d e && Nat.eqb q r
  | _,_ => false end.
Lemma image_eqb_sound x y : image_eqb x y = true -> x = y.
Proof.
  destruct x as [[[w d] q]|], y as [[[v e] r]|]; simpl; try discriminate; try reflexivity.
  intro H. apply andb_true_iff in H as [H Hq].
  apply andb_true_iff in H as [Hw Hd].
  apply Bool.eqb_prop in Hw. apply Nat.eqb_eq in Hq.
  destruct d,e; simpl in Hd; try discriminate; subst; reflexivity.
Qed.
Definition stopped (x : option N.action) := match x with None => true | _ => false end.
Definition row_ok (q : nat) :=
  image_eqb (K215F.TM230.tmn (relabel q) false) (image (N.old q false)) &&
  image_eqb (K215F.TM230.tmn (relabel q) true) (image (N.old q true)) &&
  Nat.leb (relabel q) 230 &&
  Bool.eqb (stopped (N.old q false)) (Nat.eqb q 254) &&
  Bool.eqb (stopped (N.old q true)) (Nat.eqb q 254).
Lemma all_rows_ok : forallb row_ok old_labels = true.
Proof. vm_compute. reflexivity. Qed.
Lemma active_row_ok q : active q -> row_ok q = true.
Proof.
  intro H. apply active_in in H. pose proof all_rows_ok as HH.
  rewrite forallb_forall in HH. exact (HH _ H).
Qed.
Lemma row_facts q : active q ->
  ((image_eqb (K215F.TM230.tmn (relabel q) false) (image (N.old q false)) = true /\
    image_eqb (K215F.TM230.tmn (relabel q) true) (image (N.old q true)) = true) /\
    Nat.leb (relabel q) 230 = true) /\
    Bool.eqb (stopped (N.old q false)) (Nat.eqb q 254) = true /\
    Bool.eqb (stopped (N.old q true)) (Nat.eqb q 254) = true.
Proof.
  intro H. apply active_row_ok in H. unfold row_ok in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.
Lemma table_commutes q b : active q ->
  K215F.TM230.tmn (relabel q) b = image (N.old q b).
Proof.
  intro H. apply row_facts in H. destruct H as [[[Hf Ht] Hb] [Hs Hs']].
  apply image_eqb_sound. destruct b; assumption.
Qed.
Lemma active_relabel_bound q : active q -> relabel q <= 230.
Proof.
  intro H. apply row_facts in H. destruct H as [[[Hf Ht] Hb] [Hs Hs']].
  apply Nat.leb_le; exact Hb.
Qed.
Lemma active_stop q b : active q -> (N.old q b = None <-> q = 254).
Proof.
  intro H. apply row_facts in H. destruct H as [H [Hf Ht]].
  assert (E : stopped (N.old q b) = Nat.eqb q 254).
  { apply Bool.eqb_prop. destruct b; assumption. }
  split; intro Hs.
  - apply Nat.eqb_eq. rewrite <- E. rewrite Hs. reflexivity.
  - assert (Eq : Nat.eqb q 254 = true) by (apply Nat.eqb_eq; exact Hs).
    rewrite Eq in E. destruct (N.old q b); simpl in E; [discriminate|reflexivity].
Qed.
Definition target_ok (e : N.entry) : bool :=
  match e with N.E _ _ (N.A _ _ z) => existsb (Nat.eqb z) old_labels end.
Lemma all_targets_ok : forallb target_ok N.old_rows = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lookup_member q b es a : N.lookup q b es = Some a -> In (N.E q b a) es.
Proof.
  induction es as [|[s x v] es IH]; simpl; [discriminate|].
  destruct (Nat.eqb q s && Bool.eqb b x)%bool eqn:E.
  - apply andb_true_iff in E as [Eq Ex]. apply Nat.eqb_eq in Eq.
    apply Bool.eqb_prop in Ex. intros H; inversion H; subst. left; reflexivity.
  - intro H. right. apply IH, H.
Qed.

Lemma active_target q b w d z : N.old q b = Some (N.A w d z) -> active z.
Proof.
  intro E. unfold N.old in E. apply lookup_member in E.
  pose proof all_targets_ok as H. rewrite forallb_forall in H.
  exact (H _ E).
Qed.

CoInductive stream_related (l : N.stream) (r : Stream bool) : Prop :=
| streams_observe : N.hd l = Streams.hd r ->
    stream_related (N.tl l) (Streams.tl r) -> stream_related l r.
Lemma streams_cons b l r : stream_related l r ->
  stream_related (N.Cons b l) (Streams.Cons b r).
Proof. intro H. constructor; [reflexivity|exact H]. Qed.

Inductive configs_related : N.config -> (K215F.TM230.Ctx230.Q * (Stream bool * bool * Stream bool)) -> Prop :=
| configs_intro q l b r left right :
    active q -> stream_related l left -> stream_related r right ->
    configs_related (N.C q l b r)
      (K215F.TM230.st (relabel q), (left,b,right)).

Lemma related_halted c s : configs_related c s ->
  (N.state c = 254 <-> S.halted K215F.TM230.tm s).
Proof.
  intros H; destruct H as [q l b r left right Hq Hl Hr].
  change (q = 254 <-> K215F.TM230.tm (K215F.TM230.st (relabel q),b) = None).
  rewrite <- (active_stop q b Hq).
  unfold K215F.TM230.tm, K215F.TM230.st.
  rewrite K215F.TM230.bval_bmk by (apply active_relabel_bound; exact Hq).
  rewrite table_commutes by exact Hq.
  destruct (N.old q b) as [[w d z]|]; simpl; [split; discriminate|tauto].
Qed.

Lemma native_step_sparse c s : configs_related c s -> N.state c <> 254 ->
  exists s', S.step K215F.TM230.tm s s' /\
             configs_related (N.step N.old c) s'.
Proof.
  intros H Hnh. destruct H as [q l b r left right Hq Hl Hr].
  change (q <> 254) in Hnh.
  destruct (N.old q b) as [[w d z]|] eqn:E.
  2: { exfalso. apply Hnh. apply (active_stop q b Hq). exact E. }
  assert (Hz : active z) by (eapply active_target; exact E).
  assert (Et : K215F.TM230.tm (K215F.TM230.st (relabel q), b) =
       Some (w,direction d,K215F.TM230.st (relabel z))).
  { apply K215F.TM230.tm_st. rewrite table_commutes by exact Hq. rewrite E. reflexivity. }
  destruct l as [a ll], left as [x LL], r as [a' rr], right as [y RR].
  inversion Hl as [Ha Hll]. inversion Hr as [Hb Hrr].
  cbn [N.hd N.tl Streams.hd Streams.tl] in Ha,Hb,Hll,Hrr. subst x y.
  unfold N.step. rewrite E. destruct d; cbn [N.act direction] in *.
  - eexists. split.
    + eapply S.step_left. exact Et.
    + apply configs_intro; [exact Hz|exact Hll|apply streams_cons; assumption].
  - eexists. split.
    + eapply S.step_right. exact Et.
    + apply configs_intro; [exact Hz|apply streams_cons; assumption|exact Hrr].
Qed.

Lemma sparse_step_native c s s' : configs_related c s ->
  S.step K215F.TM230.tm s s' -> configs_related (N.step N.old c) s'.
Proof.
  intros H E.
  destruct (Nat.eq_dec (N.state c) 254) as [Hhalt|Hlive].
  - exfalso. eapply S.halted_no_step; [apply (proj1 (related_halted c s H)); exact Hhalt|exact E].
  - destruct (native_step_sparse c s H Hlive) as [t [Et Rt]].
    assert (s'=t) by (eapply S.step_deterministic; [exact E|exact Et]). subst. exact Rt.
Qed.

Lemma run_first m n c : N.run m (Datatypes.S n) c = N.run m n (N.step m c).
Proof.
  induction n; [reflexivity|].
  change (N.step m (N.run m (Datatypes.S n) c) = N.step m (N.run m n (N.step m c))).
  rewrite IHn. reflexivity.
Qed.

Lemma native_halts_sparse c s : configs_related c s ->
  N.halts N.old c -> S.halts K215F.TM230.tm s.
Proof.
  intros Hr [n Hn]. revert c s Hr Hn.
  induction n as [|n IH]; intros c s Hr Hn.
  - apply S.halted_halts. apply (proj1 (related_halted c s Hr)). exact Hn.
  - destruct (Nat.eq_dec (N.state c) 254) as [Hhalt|Hlive].
    + apply S.halted_halts. apply (proj1 (related_halted c s Hr)). exact Hhalt.
    + destruct (native_step_sparse c s Hr Hlive) as [s' [Hs Hr']].
      eapply S.halts_step; [|exact Hs].
      apply (IH _ _ Hr'). rewrite <- run_first. exact Hn.
Qed.

Lemma sparse_run_native n s s' : S.multistep K215F.TM230.tm n s s' ->
  forall c, configs_related c s -> configs_related (N.run N.old n c) s'.
Proof.
  intro H. induction H as [s|n s mid fin E H IH]; intros c R.
  - exact R.
  - rewrite run_first. apply IH. eapply sparse_step_native; eassumption.
Qed.

Lemma sparse_halts_native c s : configs_related c s ->
  S.halts K215F.TM230.tm s -> N.halts N.old c.
Proof.
  intros R [n [t [Hrun Hhalt]]]. exists n.
  pose proof (sparse_run_native n s t Hrun c R) as Rt.
  apply (proj2 (related_halted _ _ Rt)). exact Hhalt.
Qed.

Theorem related_halts_iff c s : configs_related c s ->
  (N.halts N.old c <-> S.halts K215F.TM230.tm s).
Proof. intro R. split; [apply native_halts_sparse|apply sparse_halts_native]; exact R. Qed.

Lemma native_eta (s : N.stream) : s = N.Cons (N.hd s) (N.tl s).
Proof. destruct s; reflexivity. Qed.

Lemma blank_sides_related : stream_related N.zeros (Streams.const false).
Proof. cofix IH. constructor; [reflexivity|exact IH]. Qed.

Lemma blank_related : configs_related N.blank S.c0.
Proof.
  apply configs_intro; [vm_compute; reflexivity|apply blank_sides_related|apply blank_sides_related].
Qed.

Theorem native_blank_halts_iff_sparse :
  N.halts N.old N.blank <-> S.halts K215F.TM230.tm S.c0.
Proof. apply related_halts_iff, blank_related. Qed.

Print Assumptions table_commutes.
Print Assumptions native_blank_halts_iff_sparse.
