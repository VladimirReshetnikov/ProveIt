(** Composition of two previously checked refinements: normalized paths and
    balanced certificate lookup. The new proof refines the normalized LIST
    checker, so no new operational simulation argument is needed. *)
From Coq Require Import List Bool Arith NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
Require Import BisimMirror BalancedBisim NormalizedBisim.
Import ListNotations.

Definition nbbranch (t1 t2 : tree) (T : CTree)
    (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, getTree T j with
  | Some (l1,P1), Some (l2,P2), Some (Q1,Q2) =>
      cnt_eq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _,_,_ => false
  end.

Lemma nbbranch_flatten t1 t2 T (HT : valid T) A B j :
  nbbranch t1 t2 T A B j = nbranch_ok t1 t2 (flatten T) A B j.
Proof. unfold nbbranch, nbranch_ok. now rewrite getTree_flatten. Qed.

Definition nbentry (t1 t2 : tree) (T : CTree) (x : entry) : bool :=
  let '(P1,P2,j,k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt,_), Some (EHalt,_) => true
  | Some (EDecnz r1,Q1), Some (EDecnz r2,Q2) =>
      Nat.eqb r1 r2 && nbbranch t1 t2 T (inc_path Q1) (inc_path Q2) j &&
      nbbranch t1 t2 T (brk 1 Q1) (brk 1 Q2) k
  | _,_ => false
  end.

Lemma nbentry_flatten t1 t2 T (HT : valid T) x :
  nbentry t1 t2 T x = nentry_ok t1 t2 (flatten T) x.
Proof.
  destruct x as [[[P1 P2] j] k]. unfold nbentry, nentry_ok.
  destruct (tsite t1 P1) as [[e1 Q1]|]; [|reflexivity].
  destruct (tsite t2 P2) as [[e2 Q2]|]; [|destruct e1; reflexivity].
  destruct e1; destruct e2; try reflexivity.
  now rewrite !nbbranch_flatten.
Qed.

Definition nbcheck (t1 t2 : tree) (T : CTree) : bool :=
  nbbranch t1 t2 T [] [] 0 && allTree (nbentry t1 t2 T) T.

Theorem nbcheck_refines t1 t2 T (HT : valid T) :
  nbcheck t1 t2 T = ncheck t1 t2 (flatten T).
Proof.
  unfold nbcheck, ncheck. rewrite nbbranch_flatten by exact HT.
  rewrite allTree_flatten. f_equal.
  apply forallb_pointwise. intros x. now apply nbentry_flatten.
Qed.

Theorem nbcheck_halts_iff p1 p2 T : validb T = true ->
  nbcheck (ptree p1) (ptree p2) T = true -> forall R,
  rm_halts p1 ([],R) <-> rm_halts p2 ([],R).
Proof.
  intros HT HC R. apply validb_sound in HT.
  rewrite nbcheck_refines in HC by exact HT.
  exact (ncheck_one_sided_iff p1 p2 (flatten T) HC R).
Qed.

Print Assumptions nbcheck_refines.
Print Assumptions nbcheck_halts_iff.
