(**
  Metalevel coding and scheduling for finite Skolem programs.

  This file contains no PA syntax.  It supplies the well-founded code layer
  needed by a later fixed beta-trace formula.  The polynomial pairing

      pair(a,b) = (a+b)^2 + a

  is injective and dominates both coordinates.  Every constructor is coded
  as [1 + pair(tag,payload)], so every recursive child code is strictly less
  than its parent.  A bounded-search inverse schedules every natural number;
  malformed codes deterministically schedule the zero instruction.
*)

From Stdlib Require Import List Arith Lia Bool.
From PAFiniteBasisReduction Require Import FiniteSkolemHull.

Import ListNotations.
Import PAFiniteSkolemHull.

Module PASkolemProgramCode.

Definition polynomialPair (a b : nat) : nat :=
  (a + b) * (a + b) + a.

Lemma polynomialPair_left_le : forall a b,
  a <= polynomialPair a b.
Proof. intros a b. unfold polynomialPair. nia. Qed.

Lemma polynomialPair_right_le : forall a b,
  b <= polynomialPair a b.
Proof. intros a b. unfold polynomialPair. nia. Qed.

Lemma polynomialPair_diagonal_bounds : forall a b,
  let s := a + b in
  s * s <= polynomialPair a b < S s * S s.
Proof.
  intros a b s.
  unfold polynomialPair, s.
  nia.
Qed.

Theorem polynomialPair_injective : forall a b c d,
  polynomialPair a b = polynomialPair c d ->
  a = c /\ b = d.
Proof.
  intros a b c d heq.
  pose proof (polynomialPair_diagonal_bounds a b) as hab.
  pose proof (polynomialPair_diagonal_bounds c d) as hcd.
  set (s := a + b) in *.
  set (t := c + d) in *.
  cbn in hab, hcd.
  assert (hst : s = t).
  {
    destruct (Nat.lt_trichotomy s t) as [hlt | [he | hgt]].
    - assert (S s <= t) by lia.
      assert (S s * S s <= t * t).
      { apply Nat.mul_le_mono; assumption. }
      lia.
    - exact he.
    - assert (S t <= s) by lia.
      assert (S t * S t <= s * s).
      { apply Nat.mul_le_mono; assumption. }
      lia.
  }
  unfold polynomialPair in heq.
  fold s in heq. fold t in heq.
  assert (hac : a = c) by nia.
  split; [exact hac |].
  unfold s, t in hst.
  lia.
Qed.

Definition polynomialNode (tag payload : nat) : nat :=
  S (polynomialPair tag payload).

Lemma polynomialNode_positive : forall tag payload,
  0 < polynomialNode tag payload.
Proof. intros tag payload. unfold polynomialNode. lia. Qed.

Lemma polynomialNode_payload_lt : forall tag payload,
  payload < polynomialNode tag payload.
Proof.
  intros tag payload.
  unfold polynomialNode.
  pose proof (polynomialPair_right_le tag payload).
  lia.
Qed.

(* Every immediate child of a polynomially coded node has a strictly smaller
   code: the child's code bounds the pair it sits in, and the pair is strictly
   below the node's payload bound.  [L] selects which side of the pair the
   child occupies.  The caller first reduces the node to its pair form. *)
Ltac polynomial_child_lt L :=
  eapply Nat.le_lt_trans; [ apply L | apply polynomialNode_payload_lt ].

Lemma polynomialNode_injective : forall tag payload tag' payload',
  polynomialNode tag payload = polynomialNode tag' payload' ->
  tag = tag' /\ payload = payload'.
Proof.
  intros tag payload tag' payload' heq.
  unfold polynomialNode in heq.
  injection heq as heq.
  exact (polynomialPair_injective tag payload tag' payload' heq).
Qed.

(** Constructor tags.  They are kept as reducible numerals so the scheduler
    computes by ordinary pattern matching. *)
Definition tagSeed : nat := 0.
Definition tagZero : nat := 1.
Definition tagSucc : nat := 2.
Definition tagAdd : nat := 3.
Definition tagMul : nat := 4.
Definition tagChoose : nat := 5.
Definition tagArgsNil : nat := 6.
Definition tagArgsCons : nat := 7.

Fixpoint skolemProgramCode (p : SkolemProgram) : nat :=
  match p with
  | spSeed => polynomialNode tagSeed 0
  | spZero => polynomialNode tagZero 0
  | spSucc a => polynomialNode tagSucc (skolemProgramCode a)
  | spAdd a b => polynomialNode tagAdd
      (polynomialPair (skolemProgramCode a) (skolemProgramCode b))
  | spMul a b => polynomialNode tagMul
      (polynomialPair (skolemProgramCode a) (skolemProgramCode b))
  | spChoose i args => polynomialNode tagChoose
      (polynomialPair i (skolemProgramArgsCode args))
  end
with skolemProgramArgsCode (args : SkolemProgramArgs) : nat :=
  match args with
  | spaNil => polynomialNode tagArgsNil 0
  | spaCons p rest => polynomialNode tagArgsCons
      (polynomialPair (skolemProgramCode p)
        (skolemProgramArgsCode rest))
  end.

Lemma skolemProgramCode_positive : forall p,
  0 < skolemProgramCode p.
Proof.
  intro p. destruct p; simpl; apply polynomialNode_positive.
Qed.

Lemma skolemProgramArgsCode_positive : forall args,
  0 < skolemProgramArgsCode args.
Proof.
  intro args. destruct args; simpl; apply polynomialNode_positive.
Qed.

Lemma skolemProgramCode_succ_child : forall p,
  skolemProgramCode p < skolemProgramCode (spSucc p).
Proof.
  intro p. simpl. apply polynomialNode_payload_lt.
Qed.

Lemma skolemProgramCode_add_left : forall p q,
  skolemProgramCode p < skolemProgramCode (spAdd p q).
Proof.
  intros p q. simpl.
  polynomial_child_lt polynomialPair_left_le.
Qed.

Lemma skolemProgramCode_add_right : forall p q,
  skolemProgramCode q < skolemProgramCode (spAdd p q).
Proof.
  intros p q. simpl.
  polynomial_child_lt polynomialPair_right_le.
Qed.

Lemma skolemProgramCode_mul_left : forall p q,
  skolemProgramCode p < skolemProgramCode (spMul p q).
Proof.
  intros p q. simpl.
  polynomial_child_lt polynomialPair_left_le.
Qed.

Lemma skolemProgramCode_mul_right : forall p q,
  skolemProgramCode q < skolemProgramCode (spMul p q).
Proof.
  intros p q. simpl.
  polynomial_child_lt polynomialPair_right_le.
Qed.

Lemma skolemProgramCode_choose_index : forall i args,
  i < skolemProgramCode (spChoose i args).
Proof.
  intros i args. simpl.
  polynomial_child_lt polynomialPair_left_le.
Qed.

Lemma skolemProgramCode_choose_args : forall i args,
  skolemProgramArgsCode args < skolemProgramCode (spChoose i args).
Proof.
  intros i args. simpl.
  polynomial_child_lt polynomialPair_right_le.
Qed.

Lemma skolemProgramArgsCode_cons_head : forall p args,
  skolemProgramCode p < skolemProgramArgsCode (spaCons p args).
Proof.
  intros p args. simpl.
  polynomial_child_lt polynomialPair_left_le.
Qed.

Lemma skolemProgramArgsCode_cons_tail : forall p args,
  skolemProgramArgsCode args < skolemProgramArgsCode (spaCons p args).
Proof.
  intros p args. simpl.
  polynomial_child_lt polynomialPair_right_le.
Qed.

(** A deliberately simple, executable inverse: search the finite square
    [0..n] x [0..n].  Coordinate domination guarantees that every genuine
    pair is present in the search space for its own code. *)
Definition polynomialPairCandidates (n : nat) : list (nat * nat) :=
  list_prod (seq 0 (S n)) (seq 0 (S n)).

Definition polynomialUnpair (n : nat) : nat * nat :=
  match find
      (fun ab => Nat.eqb (polynomialPair (fst ab) (snd ab)) n)
      (polynomialPairCandidates n) with
  | Some ab => ab
  | None => (0, 0)
  end.

Lemma find_some_of_In_true : forall (A : Type) (f : A -> bool) xs x,
  In x xs -> f x = true -> exists y, find f xs = Some y.
Proof.
  intros A f xs.
  induction xs as [|a xs IH]; simpl; intros x hx hfx.
  - contradiction.
  - destruct hx as [hx | hx].
    + subst x. rewrite hfx. exists a. reflexivity.
    + destruct (f a) eqn:hfa.
      * exists a. reflexivity.
      * apply (IH x); assumption.
Qed.

Lemma polynomialPair_in_candidates : forall a b,
  In (a, b) (polynomialPairCandidates (polynomialPair a b)).
Proof.
  intros a b.
  unfold polynomialPairCandidates.
  apply in_prod_iff. split; apply in_seq; simpl; split; try lia.
  - pose proof (polynomialPair_left_le a b). lia.
  - pose proof (polynomialPair_right_le a b). lia.
Qed.

Lemma polynomialUnpair_sound : forall n,
  (exists a b, polynomialPair a b = n) ->
  polynomialPair (fst (polynomialUnpair n))
    (snd (polynomialUnpair n)) = n.
Proof.
  intros n [a [b hab]].
  unfold polynomialUnpair.
  remember (find
    (fun ab0 : nat * nat =>
      Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
    (polynomialPairCandidates n)) as found eqn:hfound.
  destruct found as [[x y] |].
  - pose proof (find_some
      (fun ab0 : nat * nat =>
        Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
      (polynomialPairCandidates n) (eq_sym hfound)) as [_ htest].
    simpl.
    apply Nat.eqb_eq. exact htest.
  - exfalso.
    assert (hin : In (a, b) (polynomialPairCandidates n)).
    {
      subst n. apply polynomialPair_in_candidates.
    }
    pose proof (find_none
      (fun ab0 : nat * nat =>
        Nat.eqb (polynomialPair (fst ab0) (snd ab0)) n)
      (polynomialPairCandidates n) (eq_sym hfound) (a, b) hin) as hfalse.
    simpl in hfalse.
    apply Nat.eqb_neq in hfalse.
    contradiction.
Qed.

Theorem polynomialUnpair_pair : forall a b,
  polynomialUnpair (polynomialPair a b) = (a, b).
Proof.
  intros a b.
  pose proof (polynomialUnpair_sound (polynomialPair a b)
    (ex_intro _ a (ex_intro _ b eq_refl))) as hsound.
  destruct (polynomialUnpair (polynomialPair a b)) as [x y] eqn:hu.
  simpl in hsound.
  destruct (polynomialPair_injective x y a b hsound) as [hx hy].
  subst x. subst y. reflexivity.
Qed.

Definition polynomialSplit (n : nat) : option (nat * nat) :=
  let ab := polynomialUnpair n in
  if Nat.eqb (polynomialPair (fst ab) (snd ab)) n
  then Some ab
  else None.

Lemma polynomialSplit_pair : forall a b,
  polynomialSplit (polynomialPair a b) = Some (a, b).
Proof.
  intros a b.
  unfold polynomialSplit.
  rewrite polynomialUnpair_pair.
  simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma polynomialSplit_sound : forall n a b,
  polynomialSplit n = Some (a, b) ->
  polynomialPair a b = n.
Proof.
  intros n a b.
  unfold polynomialSplit.
  destruct (polynomialUnpair n) as [x y]. simpl.
  destruct (Nat.eqb (polynomialPair x y) n) eqn:heq;
    intro h; inversion h; subst.
  apply Nat.eqb_eq. exact heq.
Qed.

Definition polynomialUnnode (n : nat) : option (nat * nat) :=
  match n with
  | 0 => None
  | S k => polynomialSplit k
  end.

Lemma polynomialUnnode_node : forall tag payload,
  polynomialUnnode (polynomialNode tag payload) = Some (tag, payload).
Proof.
  intros tag payload.
  unfold polynomialUnnode, polynomialNode.
  apply polynomialSplit_pair.
Qed.

Lemma polynomialUnnode_sound : forall n tag payload,
  polynomialUnnode n = Some (tag, payload) ->
  polynomialNode tag payload = n.
Proof.
  intros [|n] tag payload h; [discriminate |].
  unfold polynomialUnnode in h.
  unfold polynomialNode.
  f_equal.
  exact (polynomialSplit_sound n tag payload h).
Qed.

Inductive SkolemScheduledInstruction : Type :=
| siSeed : SkolemScheduledInstruction
| siZero : SkolemScheduledInstruction
| siSucc : nat -> SkolemScheduledInstruction
| siAdd : nat -> nat -> SkolemScheduledInstruction
| siMul : nat -> nat -> SkolemScheduledInstruction
| siChoose : nat -> nat -> SkolemScheduledInstruction
| siArgsNil : SkolemScheduledInstruction
| siArgsCons : nat -> nat -> SkolemScheduledInstruction.

(** [siZero] is both the genuine zero instruction and the deterministic
    default for malformed nodes, tags, and structured payloads. *)
Definition scheduleSkolemCode (n : nat) : SkolemScheduledInstruction :=
  match polynomialUnnode n with
  | None => siZero
  | Some (tag, payload) =>
      match tag with
      | 0 => if Nat.eqb payload 0 then siSeed else siZero
      | 1 => siZero
      | 2 => siSucc payload
      | 3 =>
          match polynomialSplit payload with
          | Some (a, b) => siAdd a b
          | None => siZero
          end
      | 4 =>
          match polynomialSplit payload with
          | Some (a, b) => siMul a b
          | None => siZero
          end
      | 5 =>
          match polynomialSplit payload with
          | Some (i, args) => siChoose i args
          | None => siZero
          end
      | 6 => if Nat.eqb payload 0 then siArgsNil else siZero
      | 7 =>
          match polynomialSplit payload with
          | Some (p, rest) => siArgsCons p rest
          | None => siZero
          end
      | _ => siZero
      end
  end.

Definition scheduledInstructionOfProgram
    (p : SkolemProgram) : SkolemScheduledInstruction :=
  match p with
  | spSeed => siSeed
  | spZero => siZero
  | spSucc a => siSucc (skolemProgramCode a)
  | spAdd a b => siAdd (skolemProgramCode a) (skolemProgramCode b)
  | spMul a b => siMul (skolemProgramCode a) (skolemProgramCode b)
  | spChoose i args => siChoose i (skolemProgramArgsCode args)
  end.

Definition scheduledInstructionOfArgs
    (args : SkolemProgramArgs) : SkolemScheduledInstruction :=
  match args with
  | spaNil => siArgsNil
  | spaCons p rest =>
      siArgsCons (skolemProgramCode p) (skolemProgramArgsCode rest)
  end.

Lemma scheduleSkolemCode_program : forall p,
  scheduleSkolemCode (skolemProgramCode p) =
  scheduledInstructionOfProgram p.
Proof.
  intro p. destruct p; cbn [skolemProgramCode
    scheduledInstructionOfProgram].
  - unfold scheduleSkolemCode. rewrite polynomialUnnode_node. reflexivity.
  - unfold scheduleSkolemCode. rewrite polynomialUnnode_node. reflexivity.
  - unfold scheduleSkolemCode. rewrite polynomialUnnode_node. reflexivity.
  - unfold scheduleSkolemCode.
    rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
  - unfold scheduleSkolemCode.
    rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
  - unfold scheduleSkolemCode.
    rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
Qed.

Lemma scheduleSkolemCode_args : forall args,
  scheduleSkolemCode (skolemProgramArgsCode args) =
  scheduledInstructionOfArgs args.
Proof.
  intro args. destruct args; cbn [skolemProgramArgsCode
    scheduledInstructionOfArgs].
  - unfold scheduleSkolemCode. rewrite polynomialUnnode_node. reflexivity.
  - unfold scheduleSkolemCode.
    rewrite polynomialUnnode_node, polynomialSplit_pair. reflexivity.
Qed.

(** Fuelled total decoders.  Program-side malformed instructions become
    [spZero]; argument-side malformed instructions become [spaNil].  The
    child-decrease lemmas above make fuel [S code] sufficient on every
    genuine encoding. *)
Fixpoint decodeSkolemProgramFuel (fuel code : nat) : SkolemProgram :=
  match fuel with
  | 0 => spZero
  | S rest =>
      match scheduleSkolemCode code with
      | siSeed => spSeed
      | siZero => spZero
      | siSucc a => spSucc (decodeSkolemProgramFuel rest a)
      | siAdd a b => spAdd
          (decodeSkolemProgramFuel rest a)
          (decodeSkolemProgramFuel rest b)
      | siMul a b => spMul
          (decodeSkolemProgramFuel rest a)
          (decodeSkolemProgramFuel rest b)
      | siChoose i args => spChoose i
          (decodeSkolemProgramArgsFuel rest args)
      | siArgsNil => spZero
      | siArgsCons _ _ => spZero
      end
  end
with decodeSkolemProgramArgsFuel (fuel code : nat) : SkolemProgramArgs :=
  match fuel with
  | 0 => spaNil
  | S rest =>
      match scheduleSkolemCode code with
      | siArgsNil => spaNil
      | siArgsCons p args => spaCons
          (decodeSkolemProgramFuel rest p)
          (decodeSkolemProgramArgsFuel rest args)
      | _ => spaNil
      end
  end.

Definition decodeSkolemProgram (code : nat) : SkolemProgram :=
  decodeSkolemProgramFuel (S code) code.

Definition decodeSkolemProgramArgs (code : nat) : SkolemProgramArgs :=
  decodeSkolemProgramArgsFuel (S code) code.

Theorem decodeSkolemCode_roundtrip_mutual :
  (forall p fuel,
    skolemProgramCode p < fuel ->
    decodeSkolemProgramFuel fuel (skolemProgramCode p) = p) /\
  (forall args fuel,
    skolemProgramArgsCode args < fuel ->
    decodeSkolemProgramArgsFuel fuel (skolemProgramArgsCode args) = args).
Proof.
  apply (SkolemProgram_mutind
    (fun p => forall fuel,
      skolemProgramCode p < fuel ->
      decodeSkolemProgramFuel fuel (skolemProgramCode p) = p)
    (fun args => forall fuel,
      skolemProgramArgsCode args < fuel ->
      decodeSkolemProgramArgsFuel fuel (skolemProgramArgsCode args) = args)).
  - intros [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program. reflexivity.
  - intros [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program. reflexivity.
  - intros p IH [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program.
    cbn [scheduledInstructionOfProgram].
    f_equal. apply IH.
    pose proof (skolemProgramCode_succ_child p). lia.
  - intros p IHp q IHq [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program.
    cbn [scheduledInstructionOfProgram].
    f_equal.
    + apply IHp. pose proof (skolemProgramCode_add_left p q). lia.
    + apply IHq. pose proof (skolemProgramCode_add_right p q). lia.
  - intros p IHp q IHq [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program.
    cbn [scheduledInstructionOfProgram].
    f_equal.
    + apply IHp. pose proof (skolemProgramCode_mul_left p q). lia.
    + apply IHq. pose proof (skolemProgramCode_mul_right p q). lia.
  - intros i args IHargs [|fuel] h; [lia |].
    cbn [decodeSkolemProgramFuel].
    rewrite scheduleSkolemCode_program.
    cbn [scheduledInstructionOfProgram].
    f_equal. apply IHargs.
    pose proof (skolemProgramCode_choose_args i args). lia.
  - intros [|fuel] h; [lia |].
    cbn [decodeSkolemProgramArgsFuel].
    rewrite scheduleSkolemCode_args. reflexivity.
  - intros p IHp args IHargs [|fuel] h; [lia |].
    cbn [decodeSkolemProgramArgsFuel].
    rewrite scheduleSkolemCode_args.
    cbn [scheduledInstructionOfArgs].
    f_equal.
    + apply IHp. pose proof (skolemProgramArgsCode_cons_head p args). lia.
    + apply IHargs.
      pose proof (skolemProgramArgsCode_cons_tail p args). lia.
Qed.

Corollary decodeSkolemProgram_code : forall p,
  decodeSkolemProgram (skolemProgramCode p) = p.
Proof.
  intro p.
  unfold decodeSkolemProgram.
  apply (proj1 decodeSkolemCode_roundtrip_mutual).
  lia.
Qed.

Corollary decodeSkolemProgramArgs_code : forall args,
  decodeSkolemProgramArgs (skolemProgramArgsCode args) = args.
Proof.
  intro args.
  unfold decodeSkolemProgramArgs.
  apply (proj2 decodeSkolemCode_roundtrip_mutual).
  lia.
Qed.

Theorem skolemProgramCode_injective : forall p q,
  skolemProgramCode p = skolemProgramCode q -> p = q.
Proof.
  intros p q heq.
  pose proof (f_equal decodeSkolemProgram heq) as h.
  now rewrite !decodeSkolemProgram_code in h.
Qed.

Theorem skolemProgramArgsCode_injective : forall args rest,
  skolemProgramArgsCode args = skolemProgramArgsCode rest -> args = rest.
Proof.
  intros args rest heq.
  pose proof (f_equal decodeSkolemProgramArgs heq) as h.
  now rewrite !decodeSkolemProgramArgs_code in h.
Qed.

Definition scheduledChildCodes
    (instruction : SkolemScheduledInstruction) : list nat :=
  match instruction with
  | siSucc a => [a]
  | siAdd a b => [a; b]
  | siMul a b => [a; b]
  | siChoose _ args => [args]
  | siArgsCons p rest => [p; rest]
  | _ => []
  end.

Lemma polynomialSplit_left_lt_node : forall tag payload a b,
  polynomialSplit payload = Some (a, b) ->
  a < polynomialNode tag payload.
Proof.
  intros tag payload a b hsplit.
  pose proof (polynomialSplit_sound payload a b hsplit) as hpayload.
  eapply Nat.le_lt_trans.
  - apply polynomialPair_left_le.
  - rewrite hpayload. apply polynomialNode_payload_lt.
Qed.

Lemma polynomialSplit_right_lt_node : forall tag payload a b,
  polynomialSplit payload = Some (a, b) ->
  b < polynomialNode tag payload.
Proof.
  intros tag payload a b hsplit.
  pose proof (polynomialSplit_sound payload a b hsplit) as hpayload.
  eapply Nat.le_lt_trans.
  - apply polynomialPair_right_le.
  - rewrite hpayload. apply polynomialNode_payload_lt.
Qed.

(** The well-foundedness invariant needed by an interpreter holds for every
    scheduled natural number, including malformed codes—not merely for the
    image of the encoder. *)
Theorem scheduled_children_smaller : forall code child,
  In child (scheduledChildCodes (scheduleSkolemCode code)) ->
  child < code.
Proof.
  intros code child.
  unfold scheduleSkolemCode.
  destruct (polynomialUnnode code) as [[tag payload] |] eqn:hnode;
    [| simpl; contradiction].
  pose proof (polynomialUnnode_sound code tag payload hnode) as hcode.
  destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; simpl.
  - destruct (payload =? 0); simpl; contradiction.
  - contradiction.
  - intros [h | []]. subst child.
    rewrite <- hcode. apply polynomialNode_payload_lt.
  - destruct (polynomialSplit payload) as [[a b] |] eqn:hsplit;
      simpl; [| contradiction].
    intros [h | [h | []]]; subst child; rewrite <- hcode.
    + exact (polynomialSplit_left_lt_node 3 payload a b hsplit).
    + exact (polynomialSplit_right_lt_node 3 payload a b hsplit).
  - destruct (polynomialSplit payload) as [[a b] |] eqn:hsplit;
      simpl; [| contradiction].
    intros [h | [h | []]]; subst child; rewrite <- hcode.
    + exact (polynomialSplit_left_lt_node 4 payload a b hsplit).
    + exact (polynomialSplit_right_lt_node 4 payload a b hsplit).
  - destruct (polynomialSplit payload) as [[i args] |] eqn:hsplit;
      simpl; [| contradiction].
    intros [h | []]. subst child. rewrite <- hcode.
    exact (polynomialSplit_right_lt_node 5 payload i args hsplit).
  - destruct (payload =? 0); simpl; contradiction.
  - destruct (polynomialSplit payload) as [[p rest] |] eqn:hsplit;
      simpl; [| contradiction].
    intros [h | [h | []]]; subst child; rewrite <- hcode.
    + exact (polynomialSplit_left_lt_node 7 payload p rest hsplit).
    + exact (polynomialSplit_right_lt_node 7 payload p rest hsplit).
  - contradiction.
Qed.

Theorem scheduled_program_children_smaller : forall p child,
  In child
      (scheduledChildCodes (scheduleSkolemCode (skolemProgramCode p))) ->
  child < skolemProgramCode p.
Proof.
  intros p child.
  rewrite scheduleSkolemCode_program.
  destruct p; simpl; intro h; try contradiction.
  - destruct h as [h | []]. subst child.
    apply skolemProgramCode_succ_child.
  - destruct h as [h | [h | []]]; subst child.
    + apply skolemProgramCode_add_left.
    + apply skolemProgramCode_add_right.
  - destruct h as [h | [h | []]]; subst child.
    + apply skolemProgramCode_mul_left.
    + apply skolemProgramCode_mul_right.
  - destruct h as [h | []]. subst child.
    apply skolemProgramCode_choose_args.
Qed.

Theorem scheduled_args_children_smaller : forall args child,
  In child
      (scheduledChildCodes (scheduleSkolemCode
        (skolemProgramArgsCode args))) ->
  child < skolemProgramArgsCode args.
Proof.
  intros args child.
  rewrite scheduleSkolemCode_args.
  destruct args; simpl; intro h; try contradiction.
  destruct h as [h | [h | []]]; subst child.
  - apply skolemProgramArgsCode_cons_head.
  - apply skolemProgramArgsCode_cons_tail.
Qed.

End PASkolemProgramCode.
