(** Optimized dominated-implication proof, generated from a checked Lean graph.
    78 schematic lemmas replace the current 629-node expanded replay.
    The emitter is untrusted: every step below is an ordinary kernel proof.
    The selected graph and unchanged public API are recorded in the packet. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230.
Import ListNotations.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Module Optimized.
Lemma wim00 : wim 0 0 = 0. Proof. reflexivity. Qed.
Lemma le_l {u x} y : u <= x -> u <= wim x y.
Proof. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y} x : u <= y -> u <= wim x y.
Proof. unfold wim. pose proof (P_ge_r x y). lia. Qed.
Local Opaque wim.
Section Derivation.
Variable T : nat -> Prop.
Variable h : DomImp T.

Lemma cd0 (v0 v1 v2 v3 : nat) (hb0 : v1 <= v2) :
  T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))).
Proof. exact ltac:(let H := fresh "norm" in pose proof (ltac:(let H := fresh "norm" in pose proof ((drho8 h v2 v3 v0 v1 hb0)) as H; cbv delta [rho8] in H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H)) as H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H). Qed.

Lemma b0 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))).
Proof. exact (cd0 v0 v1 v1 v2 (Nat.le_refl _)). Qed.

Lemma b1 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))).
Proof. exact (cd0 v0 v1 (wim v2 v1) v3 (le_r v2 (Nat.le_refl _))). Qed.

Lemma b3 (v0 v1 v2 : nat) :
  T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 v1)) (wim v2 (wim v1 v1))).
Proof. exact (dmp h _ _ (b1 (wim v1 v1) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b1 v1 v1 v0 v0)). Qed.

Lemma b4 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 (wim v1 v1)) (wim (wim (wim v2 v1) v1) (wim v2 v1))) (wim v3 (wim (wim (wim v2 v1) v1) (wim v2 v1)))).
Proof. exact (dmp h _ _ (b1 (wim (wim (wim v2 v1) v1) (wim v2 v1)) (wim v1 v1) v0 v3) (b3 v2 v1 v0)). Qed.

Lemma b10 (v0 v1 : nat) :
  T (wim v0 (wim (wim (wim v1 v1) v1) (wim v1 v1))).
Proof. exact (dmp h _ _ (b4 (wim v1 v1) v1 v1 v0) (b1 v1 v1 v1 v1)). Qed.

Lemma b12 (v0 : nat) :
  T (wim (wim (wim v0 v0) v0) (wim v0 v0)).
Proof. exact (dmp h _ _ (b10 0 v0) (dtruth h)). Qed.

Lemma b13 (v0 v1 : nat) :
  T (wim (wim (wim v0 v0) (wim v0 v0)) (wim v1 (wim v0 v0))).
Proof. exact (dmp h _ _ (b1 (wim v0 v0) v0 v0 v1) (b12 v0)). Qed.

Lemma b14 (v0 v1 : nat) :
  T (wim v0 (wim (wim v1 v1) (wim v1 v1))).
Proof. exact (dmp h _ _ (b13 (wim v1 v1) v0) (b13 v1 (wim v1 v1))). Qed.

Lemma b15 (v0 : nat) :
  T (wim (wim v0 v0) (wim v0 v0)).
Proof. exact (dmp h _ _ (b14 0 v0) (dtruth h)). Qed.

Lemma b16 (v0 v1 : nat) :
  T (wim v0 (wim v1 v1)).
Proof. exact (dmp h _ _ (b13 v1 v0) (b15 v1)). Qed.

Lemma basisI (a : nat) :
  T (wim a a).
Proof. exact (dmp h _ _ (b16 0 a) ltac:(let H := fresh "norm" in pose proof ((b12 0)) as H; cbv delta [rho8] in H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H)). Qed.

Lemma b18 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact (dmp h _ _ (b1 v0 v1 v0 v2) (basisI (wim v0 v1))). Qed.

Lemma b19 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact (dmp h _ _ (b1 (wim v1 v2) v1 v0 v3) (b18 v1 v2 v0)). Qed.

Lemma b20 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact (dmp h _ _ (b1 (wim v3 v1) (wim v1 v2) v0 v4) (b19 v3 v1 v2 v0)). Qed.

Lemma b21 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact (dmp h _ _ (b20 (wim v2 v3) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (b1 v2 v3 (wim v1 v2) v1)). Qed.

Lemma b22 (v0 v1 v2 : nat) :
  T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact (dmp h _ _ (b21 0 v0 v1 v2) (dtruth h)). Qed.

Lemma b23 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact (dmp h _ _ (b1 (wim (wim v0 v1) v2) v1 v0 v3) (b22 v0 v1 v2)). Qed.

Lemma b24 (v0 v1 v2 : nat) :
  T (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact (dmp h _ _ (b23 (wim v1 v2) v1 v1 v0) (b18 v1 v2 (wim (wim v1 v2) v1))). Qed.

Lemma basisP (a b : nat) :
  T (wim (wim (wim a b) a) a).
Proof. exact (dmp h _ _ (b24 0 a b) ltac:(let H := fresh "norm" in pose proof ((b12 0)) as H; cbv delta [rho8] in H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H)). Qed.

Lemma b26 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact (dmp h _ _ (b0 (wim v0 v1) v0 v2) (basisP v0 v1)). Qed.

Lemma b27 (v0 v1 v2 : nat) :
  T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact (dmp h _ _ (b23 v1 (wim v1 v2) (wim v1 v2) v0) (b26 v1 v2 (wim v1 (wim v1 v2)))). Qed.

Lemma b28 (v0 v1 : nat) :
  T (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact (dmp h _ _ (b27 0 v0 v1) (dtruth h)). Qed.

Lemma b29 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact (dmp h _ _ (b1 v1 (wim v1 v2) v0 v3) (b26 v1 v2 v0)). Qed.

Lemma b30 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact (dmp h _ _ (b28 (wim (wim v0 (wim v1 v2)) v1) v1) (b29 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1))). Qed.

Lemma b33 (v0 v1 v2 v3 : nat) :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact (dmp h _ _ (b0 (wim v1 (wim v0 v2)) v0 v3) (b30 v1 v0 v2)). Qed.

Lemma b35 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))).
Proof. exact (dmp h _ _ (b28 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (b33 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2))))). Qed.

Lemma b36 (v0 v1 v2 v3 v4 v5 : nat) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact (dmp h _ _ (b1 (wim v3 (wim v2 v4)) (wim v1 v2) v0 v5) (b20 v3 v2 v4 v1 v0)). Qed.

Lemma b38 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact (dmp h _ _ (b36 (wim v3 v2) v1 v2 (wim (wim v1 v2) v3) v3 v0) (b1 v3 v2 v1 v2)). Qed.

Lemma b39 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact (dmp h _ _ (b35 v1 (wim (wim v0 v1) v2) v2) (b38 v1 v0 v1 v2)). Qed.

Lemma b40 (v0 v1 v2 : nat) :
  T (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (dmp h _ _ (b39 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (b0 v1 v0 v2)). Qed.

Lemma b41 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))).
Proof. exact (dmp h _ _ (b39 v1 v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) (b40 (wim v1 v0) v2 v3)). Qed.

Lemma b42 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact (dmp h _ _ (cd0 v0 v1 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 (le_l (wim v3 v2) (le_l v2 (le_r v0 (Nat.le_refl _))))) (b40 (wim v0 v1) v2 v3)). Qed.

Lemma b44 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact (dmp h _ _ (b28 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (b42 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0))). Qed.

Lemma b45 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact (dmp h _ _ (b0 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 v4) (b44 v0 v1 v2 v3)). Qed.

Lemma b50 (v0 v1 v2 v3 v4 v5 : nat) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact (dmp h _ _ (b1 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) v0 v5) (b45 v1 v2 v3 v4 v0)). Qed.

Lemma b51 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact (dmp h _ _ (b28 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (b50 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1))). Qed.

Lemma cd47 (v0 v1 v2 : nat) (hb0 : v2 <= v0) :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (dmp h _ _ (b35 (wim (wim v1 v2) v0) (wim v0 v1) v1) (cd0 v1 v2 v0 (wim (wim v1 v2) v0) (Nat.le_trans _ _ _ (Nat.le_refl _) (Nat.le_trans _ _ _ hb0 (Nat.le_refl _))))). Qed.

Lemma cd52 (v0 v1 v2 v3 : nat) (hb0 : v3 <= v0) :
  T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ltac:(let H := fresh "norm" in pose proof ((dmp h _ _ (cd47 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (b40 v0 v1 v2))) as H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H). Qed.

Lemma b52 (v0 v1 v2 v3 : nat) :
  T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact (dmp h _ _ (cd52 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (Nat.le_refl _)) (b51 (wim v0 (wim v1 v2)) v0 v3 v2 v1)). Qed.

Lemma b53 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3))).
Proof. exact (dmp h _ _ (b52 v0 (wim (wim v4 v0) v3) (wim v2 v3) v1) (b41 v0 v4 v3 v2)). Qed.

Lemma cd60 (v0 v1 v2 v3 : nat) (hb0 : v3 <= (wim v1 (wim v1 v2))) :
  T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact ltac:(let H := fresh "norm" in pose proof ((dmp h _ _ (cd47 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (b26 v1 v2 v0))) as H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H). Qed.

Lemma cd92 (v0 v1 v2 : nat) :
  T (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact (dmp h _ _ (cd60 v0 (wim (wim v1 v0) v2) v2 (wim (wim (wim v1 v0) v2) v2) (le_r (wim (wim v1 v0) v2) (Nat.le_refl _))) (b53 v0 (wim (wim (wim v1 v0) v2) v2) (wim (wim v1 v0) v2) v2 v1)). Qed.

Lemma cd75 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact (dmp h _ _ (b52 v0 (wim (wim v3 v0) v2) v2 v1) (cd92 v0 v3 v2)). Qed.

Lemma cd93 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) (wim v4 v1)).
Proof. exact (dmp h _ _ (cd0 v1 v2 (wim (wim (wim v0 (wim v1 v2)) v3) v3) v4 (le_l v3 (le_l v3 (le_r v0 (le_r v1 (Nat.le_refl _)))))) (cd92 (wim v1 v2) v0 v3)). Qed.

Lemma cd94 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1).
Proof. exact (dmp h _ _ (b28 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1) (cd93 v0 v1 v2 v3 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1))). Qed.

Lemma cd84 (v0 v1 v2 v3 v4 : nat) :
  T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2) v2).
Proof. exact (dmp h _ _ (cd75 (wim (wim (wim v1 (wim v2 v3)) v4) v4) v2 v2 v0) (cd94 v1 v2 v3 v4)). Qed.

Lemma cd85 (v0 v1 v2 v3 : nat) :
  T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact (dmp h _ _ (cd52 v0 v1 (wim (wim v2 (wim v0 v3)) v1) v0 (Nat.le_refl _)) (cd84 (wim v0 v1) v2 v0 v3 v1)). Qed.

Lemma b56 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1).
Proof. exact (dmp h _ _ (cd85 (wim (wim v1 v2) v1) v1 v0 v3) (basisP v1 v2)). Qed.

Lemma b57 (v0 v1 v2 : nat) :
  T (wim (wim v0 v1) (wim (wim (wim v0 v2) v0) v1)).
Proof. exact (dmp h _ _ (cd52 v0 v1 (wim (wim v0 v2) v0) v0 (Nat.le_refl _)) (b56 (wim v0 v1) v0 v2 v1)). Qed.

Lemma cd61 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) (wim v3 v2))).
Proof. exact (dmp h _ _ (b57 v0 (wim (wim v0 v2) (wim v3 v2)) v1) (b40 v0 v2 v3)). Qed.

Lemma cd62 (v0 v1 : nat) :
  T (wim v0 (wim (wim v0 v1) v1)).
Proof. exact (dmp h _ _ (cd60 v0 (wim v0 v1) v1 v0 (le_l (wim (wim v0 v1) v1) (le_l v1 (Nat.le_refl _)))) (cd61 v0 (wim (wim v0 v1) v1) v1 (wim v0 v1))). Qed.

Lemma cd63 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) v2)).
Proof. exact (dmp h _ _ (b57 v0 (wim (wim v0 v2) v2) v1) (cd62 v0 v2)). Qed.

Lemma cd64 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))).
Proof. exact (dmp h _ _ (cd0 (wim v0 v2) v0 (wim (wim v0 v1) v1) v3 (le_l v1 (le_l v1 (Nat.le_refl _)))) (cd63 v0 v2 v1)). Qed.

Lemma cd30 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v3 (wim v2 v0))).
Proof. exact (dmp h _ _ (b1 (wim v2 v0) v1 v0 v3) (b39 v2 v0 v1)). Qed.

Lemma cd31 (v0 v1 v2 : nat) :
  T (wim v0 (wim v1 (wim v2 v0))).
Proof. exact (dmp h _ _ (b22 v0 (wim v1 (wim v2 v0)) (wim v2 v0)) (cd30 v0 (wim v1 (wim v2 v0)) v2 v1)). Qed.

Lemma cd66 (v0 v1 v2 v3 : nat) (hb0 : v3 <= v2) :
  T (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))).
Proof. exact ltac:(let H := fresh "norm" in pose proof ((dmp h _ _ (cd47 v2 (wim v0 (wim v1 v2)) v3 hb0) (cd31 v2 v0 v1))) as H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H). Qed.

Lemma cd35 (v0 v1 v2 v3 : nat) :
  T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))).
Proof. exact (dmp h _ _ (cd66 (wim v0 (wim v1 (wim v2 (wim v0 v3)))) v1 (wim v2 (wim v0 v3)) (wim v0 v3) (le_r v2 (Nat.le_refl _))) (cd64 v0 (wim v1 (wim v2 (wim v0 v3))) v3 v2)). Qed.

Lemma cd65 (v0 v1 v2 : nat) :
  T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)).
Proof. exact (dmp h _ _ (b28 (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) (cd64 v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2)))). Qed.

Lemma cd67 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))).
Proof. exact (dmp h _ _ (cd66 v0 v1 (wim (wim v0 v2) (wim v3 v2)) v0 (le_l (wim v3 v2) (le_l v2 (Nat.le_refl _)))) (cd61 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v2 v3)). Qed.

Lemma cd68 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))).
Proof. exact (dmp h _ _ (cd65 v0 v1 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) (cd67 (wim (wim v0 v1) v1) v0 v2 v3)). Qed.

Lemma cd69 (v0 v1 v2 : nat) :
  T (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)).
Proof. exact (dmp h _ _ (b35 v0 (wim (wim (wim v0 v1) v1) v2) v2) (cd68 v0 v1 v2 v0)). Qed.

Lemma cd76 (v0 v1 v2 : nat) (hb0 : v2 <= v0) :
  T (wim (wim (wim (wim (wim v0 v1) v1) v2) v0) (wim (wim v0 v1) v1)).
Proof. exact ltac:(let H := fresh "norm" in pose proof ((dmp h _ _ (cd47 v0 (wim (wim v0 v1) v1) v2 hb0) (cd62 v0 v1))) as H; repeat rewrite wim00 in H; repeat rewrite wim00; exact H). Qed.

Lemma cd77 (v0 v1 v2 : nat) :
  T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)).
Proof. exact (dmp h _ _ (b28 (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) (cd30 v0 v1 v2 (wim (wim v0 v1) (wim v2 v0)))). Qed.

Lemma cd80 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)).
Proof. exact (dmp h _ _ (cd69 v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) (cd92 (wim (wim v0 v2) v2) v1 v3)). Qed.

Lemma cd81 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1) v1).
Proof. exact (dmp h _ _ (cd77 v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1)) (cd80 (wim v1 v2) v0 v3 v1)). Qed.

Lemma cd82 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact (dmp h _ _ (cd76 v0 (wim (wim (wim v0 v1) v2) v2) v0 (Nat.le_refl _)) (cd81 (wim v0 (wim (wim (wim v0 v1) v2) v2)) v0 v1 v2)). Qed.

Lemma cd86 (v0 v1 v2 : nat) :
  T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact (dmp h _ _ (cd82 (wim v0 v1) (wim v0 v2) v1) (cd85 v0 v1 (wim v0 v1) v2)). Qed.

Lemma cd87 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact (dmp h _ _ (cd75 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (cd86 v1 v2 v3)). Qed.

Lemma cd88 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact (dmp h _ _ (cd52 v0 (wim v1 v2) (wim v1 v0) v0 (Nat.le_refl _)) (cd87 (wim v0 (wim v1 v2)) v1 v0 v2)). Qed.

Lemma cd89 (v0 v1 v2 v3 : nat) :
  T (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact (dmp h _ _ (cd88 v1 v0 (wim (wim v1 v2) (wim v3 v2))) (cd67 v1 v0 v2 v3)). Qed.

Lemma cd90 (v0 v1 v2 v3 : nat) :
  T (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact (dmp h _ _ (cd69 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (cd89 (wim v0 v1) v1 v2 v3)). Qed.

Lemma cd91 (v0 v1 v2 : nat) :
  T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))).
Proof. exact (dmp h _ _ (cd35 v0 (wim v0 v1) (wim v1 v2) v2) (cd90 v0 v1 v2 v0)). Qed.

Lemma cd104 (v0 v1 v2 v3 : nat) :
  T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)).
Proof. exact (dmp h _ _ (cd91 (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (cd91 v2 v0 v1)). Qed.

Lemma cd103 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))).
Proof. exact (dmp h _ _ (cd104 (wim v1 v2) v2 v0 (wim v1 (wim v0 v2))) (cd69 v1 v2 (wim v0 v2))). Qed.

Lemma basisK (a b : nat) :
  T (wim a (wim b a)).
Proof. exact (dmp h _ _ (cd103 b a a) (b16 b a)). Qed.

Lemma cd105 (v0 v1 v2 : nat) :
  T (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))).
Proof. exact (dmp h _ _ (cd104 v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (cd88 (wim v1 v2) v0 v2)). Qed.

Lemma cd106 (v0 v1 v2 : nat) :
  T (wim (wim v0 (wim v1 v2)) (wim (wim v0 v1) (wim v0 v2))).
Proof. exact (dmp h _ _ (cd103 (wim v0 v1) (wim v0 (wim v1 v2)) (wim v0 v2)) (cd105 v0 v1 v2)). Qed.

Lemma composition a b c : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (cd91 a b c). Qed.
Lemma distribution a b c : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof. exact (cd106 a b c). Qed.

Inductive HypProof : list nat -> nat -> Prop :=
 | hp_ax G a : T a -> HypProof G a
 | hp_hyp G a : In a G -> HypProof G a
 | hp_mp G a b : HypProof G (wim a b) -> HypProof G a -> HypProof G b.
Arguments hp_ax {G a} _.
Arguments hp_hyp {G a} _.
Arguments hp_mp {G a b} _ _.

Lemma proof_sound G a (d : HypProof G a) :
  (forall x, In x G -> T x) -> T a.
Proof.
 induction d as [G a Ha|G a Ha|G a b d1 IH1 d2 IH2]; intro HG.
 - exact Ha.
 - exact (HG a Ha).
 - exact (dmp h _ _ (IH1 HG) (IH2 HG)).
Qed.
Arguments proof_sound {G a} _ _.

Lemma discharge_aux G' b (d : HypProof G' b) :
  forall a G, G' = a :: G -> HypProof G (wim a b).
Proof.
 induction d as [G x Hx|G x Hx|G x y d1 IH1 d2 IH2]; intros a D E.
 - exact (hp_mp (hp_ax (basisK x a)) (hp_ax Hx)).
 - subst G. simpl in Hx. destruct Hx as [Hx|Hx].
   + subst x. exact (hp_ax (basisI a)).
   + exact (hp_mp (hp_ax (basisK x a)) (hp_hyp Hx)).
 - exact (hp_mp (hp_mp (hp_ax (distribution a x y)) (IH1 a D E)) (IH2 a D E)).
Qed.
Lemma discharge G a b (d : HypProof (a :: G) b) : HypProof G (wim a b).
Proof. exact (discharge_aux _ _ d a G eq_refl). Qed.
Arguments discharge {G a b} _.

Theorem rho8_all a b c u : T (rho8 a b c u).
Proof.
 pose (f := wim (wim c u) a).
 pose (g := wim a c).
 assert (hc : HypProof [wim c u; b; g; f] c).
 { refine (hp_mp (a:=a) _ _).
   - apply hp_hyp. simpl. tauto.
   - refine (hp_mp (a:=wim c u) _ _).
     + apply hp_hyp. simpl. tauto.
     + apply hp_hyp. simpl. tauto. }
 assert (closedC : HypProof [b;g;f] c).
 { exact (hp_mp (hp_ax (basisP c u)) (discharge hc)). }
 exact (proof_sound (discharge (discharge (discharge closedC)))
   (fun x H => False_rect _ (in_nil H))).
Qed.
End Derivation.
End Optimized.

Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof. exact (Optimized.rho8_all T h a b c u). Qed.
Print Assumptions rho8_all.
Print Assumptions Optimized.composition.
Print Assumptions Optimized.distribution.
