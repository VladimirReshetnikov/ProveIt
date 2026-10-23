(** Actual K215 symbolic-step adapter. The table-parameterized body below is
    obtained by replacing only the four tmn applications in the maintained
    Runtime230Core.sstep definition. The final specialization equality is
    definitional. Compile after the K215F runtime closure has been built. *)
From Coq Require Import List Bool.
From BusyCoq Require Import TM.
From K215F Require Import TM230 Runtime230Core.
Require Import FootprintReplay.
Import ListNotations.

Definition sstepWith (table : nat * bool -> option (bool * dir * nat)) (br : branch) (s : sconf) : option (sconf * bool) :=
  let '(q, onl, l, r) := s in
  if onl then
    match l with
    | [] => Some ((q, false, [], SB false :: r), false)
    | SB x :: l => Some ((q, false, l, SB x :: r), false)
    | SR b a c :: l =>
        match table (q, b) with
        | Some (w, L, q2) => if Nat.eqb q2 q then Some ((q, true, l, SR w a c :: r), false)
                             else peel_left q b a c l r
        | _ => peel_left q b a c l r
        end
    | SBox _ :: _ => None
    end
  else
    match r with
    | [] => None
    | SB x :: r =>
        match table (q, x) with
        | Some (w, R, q2) => Some ((q2, false, SB w :: l, r), true)
        | Some (w, L, q2) => Some ((q2, true, l, SB w :: r), true)
        | None => None
        end
    | SR b a c :: r =>
        match table (q, b) with
        | Some (w, R, q2) => if Nat.eqb q2 q then Some ((q, false, SR w a c :: l, r), false)
                             else peel_right q b a c l r
        | _ => peel_right q b a c l r
        end
    | [SBox x] =>
        match oracle q br x with
        | Some (q2, x2, extra) => Some ((q2, true, (if extra then SB true :: l else l), [SBox x2]), false)
        | None =>
            match table (q, false) with
            | Some (false, L, q2) => Some ((q2, true, l, [SBox x]), true)
            | _ => None
            end
        end
    | SBox _ :: _ => None
    end.


Definition readRows (br : branch) (s : sconf) : list (nat * bool) :=
  let '(q, onl, l, r) := s in
  if onl then
    match l with SR b _ _ :: _ => [(q,b)] | _ => [] end
  else
    match r with
    | SB b :: _ => [(q,b)]
    | SR b _ _ :: _ => [(q,b)]
    | [SBox x] =>
        match oracle q br x with Some _ => [] | None => [(q,false)] end
    | _ => []
    end.

Lemma sstepWith_original br s :
  sstepWith (fun '(q,b) => tmn q b) br s = sstep br s.
Proof. reflexivity. Qed.

Lemma sstepWith_local a b br s :
  (forall k, In k (readRows br s) -> a k = b k) ->
  sstepWith a br s = sstepWith b br s.
Proof.
  intros H. destruct s as [[[q onl] l] r]. destruct onl.
  - destruct l as [|x l]; [reflexivity|].
    destruct x as [v|v a0 c|x]; try reflexivity.
    cbn [sstepWith readRows] in *.
    rewrite (H (q,v) (or_introl eq_refl)). reflexivity.
  - destruct r as [|x r]; [reflexivity|].
    destruct x as [v|v a0 c|x].
    + cbn [sstepWith readRows] in *.
      rewrite (H (q,v) (or_introl eq_refl)). reflexivity.
    + cbn [sstepWith readRows] in *.
      rewrite (H (q,v) (or_introl eq_refl)). reflexivity.
    + destruct r as [|y r]; [|reflexivity].
      cbn [sstepWith readRows] in *.
      destruct (oracle q br x) as [[[q' x'] extra]|] eqn:E;
        [reflexivity|].
      rewrite (H (q,false) (or_introl eq_refl)). reflexivity.
Qed.

Definition execWith table fuel br target s moved :=
  fp_exec (nat * bool) sconf (option (bool * dir * nat))
    (fun table => sstepWith table br) table fuel target s moved.

Definition siteFootprint table fuel br target s moved :=
  footprint (nat * bool) sconf (option (bool * dir * nat))
    (fun table => sstepWith table br) (readRows br)
    table fuel target s moved.

Lemma execWith_original fuel br target s moved :
  execWith (fun '(q,b) => tmn q b) fuel br target s moved =
  exec fuel br target s moved.
Proof.
  unfold execWith. revert s moved.
  induction fuel as [|fuel IH]; intros s moved; [reflexivity|].
  cbn [fp_exec exec]. rewrite sstepWith_original.
  destruct (if moved then target s else false); [reflexivity|].
  destruct (sstep br s) as [[s' m]|]; [apply IH|reflexivity].
Qed.

Theorem siteFootprint_replay a b fuel br target s moved :
  (forall k, In k (siteFootprint a fuel br target s moved) -> a k = b k) ->
  execWith a fuel br target s moved = execWith b fuel br target s moved.
Proof.
  intro H. apply (footprint_result (nat * bool) sconf
    (option (bool * dir * nat)) (fun table => sstepWith table br)
    (readRows br)); [|exact H].
  intros a' b' s' H'. apply sstepWith_local. exact H'.
Qed.

Print Assumptions sstepWith_local.
Print Assumptions execWith_original.
Print Assumptions siteFootprint_replay.
