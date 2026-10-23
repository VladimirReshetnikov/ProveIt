(** Algebraic frame transport for the maintained K215 symbolic executor.
    The empty-left reorientation is deliberately excluded.  This body can be
    checked with the production Runtime230Core import or with the exact
    source-extracted executor parameterized by an arbitrary transition table. *)

Definition add_left (frame : list seg) (s : sconf) : sconf :=
  let '(q, onl, l, r) := s in (q, onl, l ++ frame, r).

Definition safe_left (s : sconf) : bool :=
  let '(_, onl, l, _) := s in
  match onl, l with true, [] => false | _, _ => true end.

Definition map_frame (frame : list seg) (sm : sconf * bool) : sconf * bool :=
  let '(s, m) := sm in (add_left frame s, m).

Lemma safe_left_add_left : forall frame s,
    safe_left s = true -> safe_left (add_left frame s) = true.
Proof.
  intros frame [[[q onl] l] r].
  destruct onl; destruct l; simpl; auto; discriminate.
Qed.

Lemma peel_left_add_left : forall frame q b a c l r,
    peel_left q b a c (l ++ frame) r =
      option_map (map_frame frame) (peel_left q b a c l r).
Proof. intros. destruct c; destruct a; reflexivity. Qed.

Lemma peel_right_add_left : forall frame q b a c l r,
    peel_right q b a c (l ++ frame) r =
      option_map (map_frame frame) (peel_right q b a c l r).
Proof. intros. destruct c; destruct a; reflexivity. Qed.

(** Strong form: failure and the progress Boolean are both preserved. *)
Theorem sstep_add_left_eq : forall frame br s,
    safe_left s = true ->
    sstep br (add_left frame s) =
      option_map (map_frame frame) (sstep br s).
Proof.
  intros frame br [[[q onl] l] r] Hsafe.
  destruct onl.
  - destruct l as [|x l]; [discriminate Hsafe|].
    destruct x as [b|b a c|x]; cbn [sstep add_left app].
    + reflexivity.
    + destruct (tmn q b) as [[[w d] q2]|];
        [destruct d|]; try apply peel_left_add_left.
      destruct (Nat.eqb q2 q); [reflexivity|apply peel_left_add_left].
    + reflexivity.
  - destruct r as [|x r]; [reflexivity|].
    destruct x as [b|b a c|x]; cbn [sstep add_left app].
    + destruct (tmn q b) as [[[w d] q2]|]; [destruct d|]; reflexivity.
    + destruct (tmn q b) as [[[w d] q2]|];
        [destruct d|]; try apply peel_right_add_left.
      destruct (Nat.eqb q2 q); [reflexivity|apply peel_right_add_left].
    + destruct r as [|y r]; [|reflexivity].
      cbn [sstep].
      destruct (oracle q br x) as [[[q2 x2] extra]|].
      * destruct extra; reflexivity.
      * destruct (tmn q false) as [[[w d] q2]|];
          [destruct w; destruct d|]; reflexivity.
Qed.

Corollary sstep_add_left : forall frame br s t m,
    safe_left s = true -> sstep br s = Some (t, m) ->
    sstep br (add_left frame s) = Some (add_left frame t, m).
Proof.
  intros frame br s t m Hsafe Hstep.
  rewrite sstep_add_left_eq by exact Hsafe. rewrite Hstep. reflexivity.
Qed.

(** Fixed-length guarded execution.  A true accumulated flag certifies that
    at least one symbolic step justified a positive concrete run. *)
Fixpoint run_local (fuel : nat) (br : branch) (s : sconf)
    : option (sconf * bool) :=
  match fuel with
  | 0 => Some (s, false)
  | S k =>
      if safe_left s then
        match sstep br s with
        | None => None
        | Some (s', m) =>
            match run_local k br s' with
            | None => None
            | Some (t, m') => Some (t, orb m m')
            end
        end
      else None
  end.

Theorem run_local_add_left : forall fuel frame br s t moved,
    run_local fuel br s = Some (t, moved) ->
    run_local fuel br (add_left frame s) =
      Some (add_left frame t, moved).
Proof.
  induction fuel as [|fuel IH]; intros frame br s t moved Hrun.
  - simpl in Hrun. inversion Hrun; reflexivity.
  - simpl in Hrun.
    destruct (safe_left s) eqn:Hsafe; [|discriminate].
    destruct (sstep br s) as [[s' m]|] eqn:Hstep; [|discriminate].
    destruct (run_local fuel br s') as [[u m']|] eqn:Htail; [|discriminate].
    inversion Hrun; subst u moved.
    simpl. rewrite (safe_left_add_left frame s Hsafe).
    rewrite (sstep_add_left frame br s s' m Hsafe Hstep).
    rewrite (IH frame br s' t m' Htail). reflexivity.
Qed.

(** The guard is necessary, even for a single step and for any machine table.
    Reading an appended nonblank cell differs from inventing a blank cell. *)
Theorem unguarded_empty_left_fails : forall br,
  sstep br (add_left [SB true] (0, true, [], [])) <>
    option_map (map_frame [SB true]) (sstep br (0, true, [], [])).
Proof. intros br. discriminate. Qed.

(** Relational client interface.  All hypotheses below become explicit
    parameters of the final theorem; no global axiom is introduced. *)
Section SemanticClient.
  Context {C : Type} (view : sconf -> C).
  Context (reach reach1 : C -> C -> Prop).
  Hypothesis reach_refl : forall x, reach x x.
  Hypothesis reach_trans : forall x y z, reach x y -> reach y z -> reach x z.
  Hypothesis reach1_then : forall x y z, reach1 x y -> reach y z -> reach1 x z.
  Hypothesis then_reach1 : forall x y z, reach x y -> reach1 y z -> reach1 x z.
  Variable br : branch.
  Hypothesis one_step_sound : forall s t m,
    sstep br s = Some (t, m) ->
    reach (view s) (view t) /\ (m = true -> reach1 (view s) (view t)).

  Theorem run_local_sound : forall fuel s t moved,
    run_local fuel br s = Some (t, moved) ->
    reach (view s) (view t) /\
      (moved = true -> reach1 (view s) (view t)).
  Proof.
    induction fuel as [|fuel IH]; intros s t moved Hrun.
    - simpl in Hrun. inversion Hrun; subst t moved.
      split; [apply reach_refl|discriminate].
    - simpl in Hrun.
      destruct (safe_left s) eqn:Hsafe; [|discriminate].
      destruct (sstep br s) as [[s' m]|] eqn:Hstep; [|discriminate].
      destruct (run_local fuel br s') as [[u m']|] eqn:Htail; [|discriminate].
      inversion Hrun; subst u moved.
      destruct (one_step_sound s s' m Hstep) as [Hfirst Pfirst].
      destruct (IH s' t m' Htail) as [Hrest Prest].
      split.
      + eapply reach_trans; eassumption.
      + intro Hpos. apply Bool.orb_true_iff in Hpos.
        destruct Hpos as [Hpos|Hpos].
        * eapply reach1_then; [apply Pfirst; exact Hpos|exact Hrest].
        * eapply then_reach1; [exact Hfirst|apply Prest; exact Hpos].
  Qed.

  Corollary run_local_frame_sound : forall fuel frame s t moved,
    run_local fuel br s = Some (t, moved) ->
    reach (view (add_left frame s)) (view (add_left frame t)) /\
      (moved = true ->
        reach1 (view (add_left frame s)) (view (add_left frame t))).
  Proof.
    intros. eapply run_local_sound. eapply run_local_add_left. eassumption.
  Qed.
End SemanticClient.
