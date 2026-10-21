(* AX9 factorization and protected-tail soundness, 21 October 2026.
   Standard-library Coq 8.18. No physical Turing-machine endpoint is asserted. *)
From Coq Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Section AbstractStack.
Variable cons : nat -> nat -> nat.
Variable hd tl : nat -> nat.
Hypothesis hd_cons : forall a w, hd (cons a w) = a.
Hypothesis tl_cons : forall a w, tl (cons a w) = w.
Fixpoint prepend (xs : list nat) (w : nat) :=
  match xs with [] => w | x::ys => cons x (prepend ys w) end.
Lemma prepend_app xs ys w : prepend (xs++ys) w=prepend xs (prepend ys w).
Proof. induction xs; simpl; congruence. Qed.

Record state := State { top : nat; stack : nat; counter : nat; cache : nat }.
Definition drop (s : state) := State (cache s) (cons (top s) (stack s)) (counter s) (cache s).
Definition nip (s : state) : option state :=
  if Nat.eqb (cache s) 1 then None
  else Some (State (top s) (tl (stack s)) (counter s) (hd (stack s))).

Variable Q : nat -> nat -> nat.
(* Eight numerical logical axiom rows, independent of the incoming top/stack. *)
Variable rows : nat -> nat -> nat -> nat -> nat -> list nat.
Variable gate : nat -> nat -> nat -> nat -> nat -> nat.
Hypothesis rows_length : forall d h c x y, length (rows d h c x y)=8.
Definition payload d h c x y i := rows d h c x y ++ [Q i h].
Definition ax10 c x y s :=
  State (gate (counter s) (cache s) c x y)
    (prepend (payload (counter s) (cache s) c x y (counter s))
       (cons (top s) (stack s))) 0 0.
Definition ax9 c x y s :=
  State (gate (counter s) (cache s) c x y)
    (prepend (payload (counter s) (cache s) c x y (counter s))
       (stack s)) 0 0.
Definition ax9_biased c x y s :=
  State (gate (counter s) (cache s) c x y)
    (prepend (payload (counter s) (cache s) c x y (top s+counter s))
       (stack s)) 0 0.

(* Unrestricted factorization: clear-top AX9 has exactly the old semantics
   when preceded by DROP. No assumptions about truth, decoding or aliases. *)
Theorem ax10_factor c x y s : ax9 c x y (drop s)=ax10 c x y s.
Proof. destruct s; reflexivity. Qed.

(* The smaller no-clear source has a top-biased binder. This identity has an
   essential cache-zero premise; omitting it would be an incorrect theorem. *)
Theorem ax10_factor_zero_cache c x y t w d :
  ax9_biased c x y (drop (State t w d 0))=ax10 c x y (State t w d 0).
Proof. reflexivity. Qed.
Theorem ax10_factor_zero_top c x y w d h :
  ax9_biased c x y (State 0 (cons 0 w) d h)=ax10 c x y (State 0 w d h).
Proof. reflexivity. Qed.

Definition outcome (r : option state) (s : state) := r=None \/ r=Some s.
Fixpoint pops n s : option state :=
  match n with
  | 0 => Some s
  | S m => match nip s with None=>None | Some t=>pops m t end
  end.
Definition final_cache (xs : list nat) (h : nat) := fold_left (fun _ x => x) xs h.
Lemma final_cache_cons a xs h : final_cache (a::xs) h=final_cache xs a.
Proof. reflexivity. Qed.
Lemma final_cache_app xs ys h : final_cache (xs++ys) h=final_cache ys (final_cache xs h).
Proof. unfold final_cache. apply fold_left_app. Qed.
Theorem pop_spine xs t w d h :
  outcome (pops (length xs) (State t (prepend xs w) d h))
    (State t w d (final_cache xs h)).
Proof.
  revert t w d h. induction xs as [|a xs IH]; intros t w d h.
  - right. reflexivity.
  - simpl length. cbn [pops prepend]. unfold nip. cbn [cache stack top counter].
    destruct (Nat.eqb h 1); [left; reflexivity|].
    rewrite hd_cons,tl_cons. apply IH.
Qed.
Corollary pop_ax9_sentinel c x y t w d h b :
  outcome (pops 10 (ax9_biased c x y (State t (cons b w) d h)))
    (State (gate d h c x y) w 0 b).
Proof.
  unfold ax9_biased,payload. cbn [top stack counter cache].
  replace (prepend (rows d h c x y ++ [Q (t+d) h]) (cons b w))
    with (prepend (rows d h c x y ++ [Q (t+d) h;b]) w).
  2:{ rewrite prepend_app. simpl. rewrite prepend_app. reflexivity. }
  pose proof (pop_spine (rows d h c x y++[Q (t+d) h;b])
      (gate d h c x y) w 0 0) as H.
  rewrite app_length,rows_length in H. simpl length in H.
  rewrite final_cache_app in H. exact H.
Qed.


Variable Imp : nat -> nat -> nat.
Definition mp x s :=
  let v := counter s+x in
  if Nat.eqb (Imp (top s) v) (cache s)
  then State v (cons 0 (stack s)) v 0
  else State 0 (stack s) v 0.
Inductive command := Cdrop | Cnip | Cmp (x:nat) | Cax (c x y:nat).
Definition step k s :=
  match k with
  | Cdrop => Some (drop s)
  | Cnip => nip s
  | Cmp x => Some (mp x s)
  | Cax c x y => Some (ax9_biased c x y s)
  end.
Fixpoint run (cs:list command) s :=
  match cs with
  | [] => Some s
  | k::ks => match step k s with None=>None | Some s' => run ks s' end
  end.

(* This budget charges only compulsory DROP/NIP effects. Any MP or AX
   contribution is additional protected storage and need not be counted. *)
Inductive credit : nat -> list command -> nat -> Prop :=
| credit_nil b : credit b [] b
| credit_drop b cs e : credit (S b) cs e -> credit b (Cdrop::cs) e
| credit_nip b cs e : credit b cs e -> credit (S b) (Cnip::cs) e
| credit_mp b cs e x : credit b cs e -> credit b (Cmp x::cs) e
| credit_ax b cs e c x y : credit b cs e -> credit b (Cax c x y::cs) e.
Fixpoint pushes (cs:list command) :=
  match cs with []=>0 | Cdrop::ks=>S(pushes ks) | _::ks=>pushes ks end.
Fixpoint withdrawals (cs:list command) :=
  match cs with []=>0 | Cnip::ks=>S(withdrawals ks) | _::ks=>withdrawals ks end.
Definition prefix_counts b cs := forall pre suf, cs=pre++suf ->
  withdrawals pre <= b+pushes pre.
Lemma prefix_counts_tail b k cs : prefix_counts b (k::cs) ->
  prefix_counts
    (match k with Cdrop=>S b | Cnip=>Nat.pred b | _=>b end) cs.
Proof.
  intros H pre suf E. specialize (H (k::pre) suf).
  assert (He:k::cs=(k::pre)++suf) by (simpl;congruence).
  specialize (H He). destruct k; simpl in *; lia.
Qed.
Theorem prefix_counts_credit b cs : prefix_counts b cs -> exists e, credit b cs e.
Proof.
  revert b. induction cs as [|k cs IH]; intros b H.
  - exists b. constructor.
  - pose proof (prefix_counts_tail b k cs H) as Htail.
    destruct k.
    + destruct (IH (S b) Htail) as [e He]. exists e. constructor. exact He.
    + assert (0<b) as Hb.
      { specialize (H [Cnip] cs eq_refl). simpl in H. lia. }
      destruct b as [|b]; [lia|]. simpl in Htail.
      destruct (IH b Htail) as [e He]. exists e. constructor. exact He.
    + destruct (IH b Htail) as [e He]. exists e. constructor. exact He.
    + destruct (IH b Htail) as [e He]. exists e. constructor. exact He.
Qed.

(* An arbitrary tail is never inspected while an explicit protected head
   remains. This is the semantic bridge absent from a count-only credit lemma. *)
Section Soundness.
Variable Good : nat -> Prop.
Hypothesis Good_zero : Good 0.
Hypothesis Good_gen : forall i h, Good h -> Good (Q i h).
Hypothesis Good_rows : forall d h c x y, Good h -> Forall Good (rows d h c x y).
Hypothesis Good_gate : forall d h c x y, Good h -> Good (gate d h c x y).
Definition protected J xs s :=
  Good (top s) /\ Good (cache s) /\ Forall Good xs /\ stack s=prepend xs J.
Lemma protected_drop J xs s : protected J xs s -> protected J (top s::xs) (drop s).
Proof.
  destruct s as [t w d h]. unfold protected,drop. cbn [top cache stack prepend].
  intros [Ht [Hh [Hxs Hw]]]. repeat split; auto.
Qed.
Lemma protected_nip J a xs s s' :
  protected J (a::xs) s -> nip s=Some s' -> protected J xs s'.
Proof.
  destruct s as [t w d h]. unfold protected. cbn [top cache stack prepend].
  intros [Ht [Hh [Hxs Hw]]] E. subst w. inversion Hxs; subst.
  unfold nip in E. cbn [cache stack top counter] in E.
  destruct (Nat.eqb h 1); [discriminate|].
  rewrite hd_cons,tl_cons in E. inversion E; subst. repeat split; auto.
Qed.
Lemma protected_ax9 J xs c x y s : protected J xs s ->
  protected J (payload (counter s) (cache s) c x y (top s+counter s)++xs)
    (ax9_biased c x y s).
Proof.
  destruct s as [t w d h]. unfold protected. cbn [top cache stack counter].
  intros [Ht [Hh [Hxs Hw]]]. subst w.
  cbn [ax9_biased top stack counter cache protected]. repeat split.
  - apply Good_gate; exact Hh.
  - exact Good_zero.
  - apply Forall_app. split; [|exact Hxs]. unfold payload.
    apply Forall_app. split; [apply Good_rows;exact Hh|]. constructor.
    + apply Good_gen;exact Hh.
    + constructor.
  - rewrite prepend_app. reflexivity.
Qed.
Theorem protected_halt_refutes J xs s :
  protected J xs s -> nip s=None -> Good 1.
Proof.
  destruct s as [t w d h]. unfold protected. cbn [top cache stack].
  intros [_ [Hh _]] E. unfold nip in E. cbn [cache] in E.
  destruct (Nat.eqb h 1) eqn:H; [apply Nat.eqb_eq in H;subst;exact Hh|discriminate].
Qed.

Hypothesis Good_mp : forall a b h, Good a -> Good h -> Imp a b=h -> Good b.
Lemma protected_mp J xs x s : protected J xs s ->
  exists ys, protected J ys (mp x s) /\ length xs<=length ys.
Proof.
  destruct s as [t w d h]. unfold protected. cbn [top cache stack].
  intros [Ht [Hh [Hxs Hw]]]. subst w. unfold mp. cbn [top cache stack counter].
  destruct (Nat.eqb (Imp t (d+x)) h) eqn:E.
  - exists (0::xs). split.
    + cbn [top cache stack prepend]. repeat split; auto.
      apply (Good_mp t (d+x) h Ht Hh). apply Nat.eqb_eq in E. exact E.
    + simpl. lia.
  - exists xs. split; [cbn [top cache stack];repeat split;auto|lia].
Qed.
Theorem credit_run_sound b cs e : credit b cs e ->
  forall J xs s, protected J xs s -> b<=length xs ->
  match run cs s with
  | None => Good 1
  | Some s' => exists ys, protected J ys s' /\ e<=length ys
  end.
Proof.
  intro Hc. induction Hc; intros J xs s Hsafe Hlen.
  - cbn [run]. exists xs. auto.
  - cbn [run step]. apply IHHc with (xs:=top s::xs).
    + apply protected_drop; exact Hsafe.
    + simpl. lia.
  - cbn [run step]. destruct (nip s) as [s'|] eqn:E.
    + destruct xs as [|a xs]; [simpl in Hlen;lia|].
      apply IHHc with (xs:=xs).
      * eapply protected_nip; eauto.
      * simpl in Hlen. lia.
    + eapply protected_halt_refutes; eauto.
  - cbn [run step]. destruct (protected_mp J xs x s Hsafe) as [ys [Hy Hgrow]].
    apply IHHc with (xs:=ys); [exact Hy|lia].
  - cbn [run step].
    apply IHHc with
      (xs:=payload (counter s) (cache s) c x y (top s+counter s)++xs).
    + apply protected_ax9; exact Hsafe.
    + rewrite app_length. lia.
Qed.
Theorem zero_credit_semantic_soundness cs J t d h :
  prefix_counts 0 cs -> Good t -> Good h ->
  match run cs (State t J d h) with
  | None => Good 1
  | Some s' => exists ys, protected J ys s'
  end.
Proof.
  intros Hc Ht Hh. destruct (prefix_counts_credit 0 cs Hc) as [e He].
  assert (Hs:protected J [] (State t J d h)).
  { unfold protected. cbn [top cache stack prepend]. repeat split;auto. }
  pose proof (credit_run_sound 0 cs e He J [] (State t J d h) Hs (Nat.le_refl 0)) as H.
  destruct (run cs (State t J d h)); [destruct H as [ys [Hy _]];exists ys;exact Hy|exact H].
Qed.

(* Zero is a fixed point of pairing. For any finite trace, an arbitrarily
   long finite ghost spine of truthful zeros represents the same raw 0.
   This removes ALL scheduler-credit premises from clean-zero-stack soundness. *)
Hypothesis cons_zero : cons 0 0=0.
Lemma prepend_repeat_zero n : prepend (repeat 0 n) 0=0.
Proof. induction n; simpl; [reflexivity|]. rewrite IHn,cons_zero. reflexivity. Qed.
Lemma withdrawals_length cs : withdrawals cs<=length cs.
Proof. induction cs as [|k cs IH]; [simpl;lia|]. destruct k; simpl;lia. Qed.
Lemma length_credit cs : prefix_counts (length cs) cs.
Proof.
  intros pre suf E. subst cs. rewrite app_length.
  pose proof (withdrawals_length pre). lia.
Qed.
Theorem zero_stack_semantic_soundness cs t d h : Good t -> Good h ->
  match run cs (State t 0 d h) with
  | None => Good 1
  | Some s' => exists ys, protected 0 ys s'
  end.
Proof.
  intros Ht Hh.
  destruct (prefix_counts_credit (length cs) cs (length_credit cs)) as [e He].
  assert (Hs:protected 0 (repeat 0 (length cs)) (State t 0 d h)).
  { unfold protected. cbn [top cache stack]. repeat split;auto.
    - apply Forall_forall. intros a Ha. apply repeat_spec in Ha. subst a. exact Good_zero.
    - symmetry. apply prepend_repeat_zero. }
  assert (Hb:length cs<=length(repeat 0 (length cs))) by (rewrite repeat_length;lia).
  pose proof (credit_run_sound (length cs) cs e He 0 (repeat 0 (length cs))
               (State t 0 d h) Hs Hb) as H.
  destruct (run cs (State t 0 d h));
    [destruct H as [ys [Hy _]];exists ys;exact Hy|exact H].
Qed.
Corollary zero_stack_halt_refutes cs t d h :
  Good t -> Good h -> run cs (State t 0 d h)=None -> Good 1.
Proof.
  intros Ht Hh E. pose proof (zero_stack_semantic_soundness cs t d h Ht Hh) as H.
  rewrite E in H. exact H.
Qed.
End Soundness.
End AbstractStack.

Print Assumptions ax10_factor.
Print Assumptions ax10_factor_zero_cache.
Print Assumptions ax10_factor_zero_top.
Print Assumptions pop_ax9_sentinel.
Print Assumptions protected_nip.
Print Assumptions protected_ax9.
Print Assumptions protected_halt_refutes.

Print Assumptions prefix_counts_credit.
Print Assumptions credit_run_sound.
Print Assumptions zero_credit_semantic_soundness.

Print Assumptions zero_stack_semantic_soundness.
Print Assumptions zero_stack_halt_refutes.
