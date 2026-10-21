(** Verified binary-indexed certificates for the existing ordinary segment
    bisimulation checker.  The program semantics and soundness theorem are
    unchanged: the new checker refines Bisim230.check on the flattened tree. *)
From Coq Require Import List Bool Arith Lia NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Require Import BisimMirror.
Import ListNotations.

Inductive CTree : Type :=
| CEmpty
| CLeaf (x : entry)
| CNode (left_size : N) (l r : CTree).

Fixpoint flatten (T : CTree) : list entry :=
  match T with
  | CEmpty => []
  | CLeaf x => [x]
  | CNode _ l r => flatten l ++ flatten r
  end.

Fixpoint csize (T : CTree) : N :=
  match T with
  | CEmpty => 0%N
  | CLeaf _ => 1%N
  | CNode _ l r => (csize l + csize r)%N
  end.

Fixpoint valid (T : CTree) : Prop :=
  match T with
  | CEmpty | CLeaf _ => True
  | CNode cut l r => cut = csize l /\ valid l /\ valid r
  end.

Fixpoint validb (T : CTree) : bool :=
  match T with
  | CEmpty | CLeaf _ => true
  | CNode cut l r => N.eqb cut (csize l) && validb l && validb r
  end.

Fixpoint lookup (T : CTree) (j : N) : option entry :=
  match T with
  | CEmpty => None
  | CLeaf x => if N.eqb j 0 then Some x else None
  | CNode cut l r =>
      if N.ltb j cut then lookup l j else lookup r (j - cut)%N
  end.

Fixpoint allTree (f : entry -> bool) (T : CTree) : bool :=
  match T with
  | CEmpty => true
  | CLeaf x => f x
  | CNode _ l r => allTree f l && allTree f r
  end.

Lemma csize_flatten T : N.to_nat (csize T) = length (flatten T).
Proof. induction T; cbn; auto. rewrite N2Nat.inj_add, app_length, IHT1, IHT2. reflexivity. Qed.

Lemma validb_sound T : validb T = true -> valid T.
Proof.
  induction T; cbn; auto.
  intros H. apply andb_prop in H as [H Hr]. apply andb_prop in H as [H Hl].
  apply N.eqb_eq in H. repeat split; auto.
Qed.

Lemma lookup_flatten T : valid T -> forall j,
  lookup T j = nth_error (flatten T) (N.to_nat j).
Proof.
  induction T as [|x|cut l IHl r IHr]; intros HT j; cbn.
  - destruct (N.to_nat j); reflexivity.
  - destruct (N.eqb j 0) eqn:E.
    + apply N.eqb_eq in E. subst j. reflexivity.
    + apply N.eqb_neq in E.
      destruct (N.to_nat j) as [|n] eqn:Hj; [|destruct n; reflexivity].
      change (N.to_nat j = N.to_nat 0) in Hj.
      apply N2Nat.inj in Hj. contradiction.
  - destruct HT as [Hcut [Hl Hr]].
    destruct (N.ltb j cut) eqn:E.
    + apply N.ltb_lt in E. rewrite IHl by exact Hl.
      symmetry. apply nth_error_app1. rewrite <- csize_flatten, <- Hcut.
      lia.
    + apply N.ltb_ge in E. rewrite IHr by exact Hr.
      rewrite nth_error_app2.
      * rewrite N2Nat.inj_sub, Hcut, csize_flatten. reflexivity.
      * rewrite <- csize_flatten, <- Hcut. lia.
Qed.

Lemma allTree_flatten f T : allTree f T = forallb f (flatten T).
Proof.
  induction T; cbn.
  - reflexivity.
  - now rewrite andb_true_r.
  - now rewrite forallb_app, IHT1, IHT2.
Qed.

Definition getTree (T : CTree) (j : N) : option (list bool * list bool) :=
  match lookup T j with Some (a,b,_,_) => Some (a,b) | None => None end.

Lemma getTree_flatten T (HT : valid T) j : getTree T j = getc (flatten T) j.
Proof. unfold getTree, getc. now rewrite lookup_flatten. Qed.

Definition branchTree (t1 t2 : tree) (T : CTree) (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, getTree T j with
  | Some (l1,P1), Some (l2,P2), Some (Q1,Q2) =>
      cnt_eq l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _,_,_ => false
  end.

Lemma branchTree_flatten t1 t2 T (HT : valid T) A B j :
  branchTree t1 t2 T A B j = branch_ok t1 t2 (flatten T) A B j.
Proof. unfold branchTree, branch_ok. now rewrite getTree_flatten. Qed.

Definition entryTree (t1 t2 : tree) (T : CTree) (x : entry) : bool :=
  let '(P1,P2,j,k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt,_), Some (EHalt,_) => true
  | Some (EDecnz r1,Q1), Some (EDecnz r2,Q2) =>
      Nat.eqb r1 r2 && branchTree t1 t2 T (inc_path Q1) (inc_path Q2) j &&
      branchTree t1 t2 T (brk 1 Q1) (brk 1 Q2) k
  | _,_ => false
  end.

Lemma entryTree_flatten t1 t2 T (HT : valid T) x :
  entryTree t1 t2 T x = entry_ok t1 t2 (flatten T) x.
Proof.
  destruct x as [[[P1 P2] j] k]. unfold entryTree, entry_ok.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|reflexivity].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; reflexivity].
  destruct e1; destruct e2; try reflexivity.
  now rewrite !branchTree_flatten.
Qed.

Definition checkTree (t1 t2 : tree) (T : CTree) : bool :=
  branchTree t1 t2 T [] [] 0 && allTree (entryTree t1 t2 T) T.

Lemma forallb_pointwise (f g : entry -> bool) (H : forall x, f x = g x) xs :
  forallb f xs = forallb g xs.
Proof. induction xs; cbn; auto. now rewrite H, IHxs. Qed.

Lemma checkTree_flatten t1 t2 T (HT : valid T) :
  checkTree t1 t2 T = check t1 t2 (flatten T).
Proof.
  unfold checkTree, check. rewrite branchTree_flatten by exact HT.
  rewrite allTree_flatten.
  f_equal. apply forallb_pointwise. intros x. now apply entryTree_flatten.
Qed.

Theorem checkTree_halts_iff p1 p2 T : validb T = true ->
  checkTree (ptree p1) (ptree p2) T = true -> forall R,
  rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros HT HC R. apply validb_sound in HT.
  rewrite checkTree_flatten in HC by exact HT.
  exact (check_one_sided_iff p1 p2 (flatten T) HC R).
Qed.

(** Untrusted construction: validity, exact flattening, and all checker
    obligations are proved independently for the resulting literal tree. *)
Fixpoint buildTree (fuel : nat) (xs : list entry) : CTree :=
  match fuel, xs with
  | _, [] => CEmpty
  | _, [x] => CLeaf x
  | 0, _ => CEmpty
  | S f, _ =>
      let k := length xs / 2 in
      CNode (N.of_nat k) (buildTree f (firstn k xs)) (buildTree f (skipn k xs))
  end.

Fixpoint height (T : CTree) : nat :=
  match T with
  | CEmpty => 0
  | CLeaf _ => 1
  | CNode _ l r => S (Nat.max (height l) (height r))
  end.

Fixpoint lookupDepth (T : CTree) (j : N) : nat :=
  match T with
  | CEmpty => 0
  | CLeaf _ => 1
  | CNode cut l r =>
      S (if N.ltb j cut then lookupDepth l j else lookupDepth r (j-cut)%N)
  end.

Lemma lookupDepth_le_height T : forall j, lookupDepth T j <= height T.
Proof.
  induction T; intros j; cbn; try lia.
  destruct (N.ltb j left_size).
  - specialize (IHT1 j). pose proof (Nat.le_max_l (height T1) (height T2)). lia.
  - specialize (IHT2 (j-left_size)%N).
    pose proof (Nat.le_max_r (height T1) (height T2)). lia.
Qed.

Print Assumptions lookup_flatten.
Print Assumptions checkTree_halts_iff.
