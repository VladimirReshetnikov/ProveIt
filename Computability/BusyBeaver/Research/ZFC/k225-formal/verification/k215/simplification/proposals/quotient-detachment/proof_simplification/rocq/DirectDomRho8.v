(** Direct dominated-rho8 derivation through pointwise lifting.
    Mirrors the ProveIt Source149 / CD230 guarded schema hierarchy.
    All numerical constructors are imported unchanged from Codes230.
    Generated proofs use only dominated rho8, truth and modus ponens. *)
From Coq Require Import Arith Lia.
From K230L Require Import Codes230.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Module Direct.
Lemma wim00 : wim 0 0 = 0.
Proof. reflexivity. Qed.
Lemma le_l {u x : nat} (y : nat) (h : u <= x) : u <= wim x y.
Proof. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y : nat} (x : nat) (h : u <= y) : u <= wim x y.
Proof. unfold wim. pose proof (P_ge_r x y). lia. Qed.
Local Opaque wim.

Section Proof.
Variable T : nat -> Prop.
Variable h : DomImp T.
Definition mp {a b : nat} : T (wim a b) -> T a -> T b := dmp h a b.

Lemma b0 (v0 v1 v2 : nat) : T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))).
Proof. exact ((drho8 h v1 v2 v0 v1 (Nat.le_refl _))). Qed.

Lemma b1 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))).
Proof. exact ((drho8 h (wim v2 v1) v3 v0 v1 (le_r v2 (Nat.le_refl _)))). Qed.

Lemma b2 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim (wim (wim v1 v2) v0) (wim v3 v0))).
Proof. exact ((drho8 h (wim v1 v2) v3 v0 v1 (le_l v2 (Nat.le_refl _)))). Qed.

Lemma b3 (v0 v1 v2 : nat) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 v1)) (wim v2 (wim v1 v1))).
Proof. exact ((mp (b1 (wim v1 v1) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b1 v1 v1 v0 v0))). Qed.

Lemma b4 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 (wim v1 v1)) (wim (wim (wim v2 v1) v1) (wim v2 v1))) (wim v3 (wim (wim (wim v2 v1) v1) (wim v2 v1)))).
Proof. exact ((mp (b1 (wim (wim (wim v2 v1) v1) (wim v2 v1)) (wim v1 v1) v0 v3) (b3 v2 v1 v0))). Qed.

Lemma b5 (v0 v1 v2 : nat) : T (wim (wim (wim v0 0) v1) (wim (wim v1 v0) (wim v2 v0))).
Proof. exact ((drho8 h v1 v2 v0 0 (Nat.le_0_l _))). Qed.

Lemma b6 (v0 v1 v2 : nat) : T (wim (wim (wim (wim 0 v0) (wim v1 v0)) (wim v0 0)) (wim v2 (wim v0 0))).
Proof. exact ((mp (b5 (wim v0 0) (wim (wim 0 v0) (wim v1 v0)) v2) (b5 v0 0 v1))). Qed.

Lemma b7 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 (wim v1 0)) (wim (wim 0 v1) (wim v2 v1))) (wim v3 (wim (wim 0 v1) (wim v2 v1)))).
Proof. exact ((mp (b1 (wim (wim 0 v1) (wim v2 v1)) (wim v1 0) v0 v3) (b6 v1 v2 v0))). Qed.

Lemma b8 (v0 : nat) : T (wim v0 0).
Proof. exact ((mp (ltac:(let Hnorm := fresh in pose proof ((b7 0 0 0 v0)) as Hnorm; repeat rewrite wim00 in Hnorm; repeat rewrite wim00; exact Hnorm) : T (wim 0 (wim v0 0))) (ltac:(let Hnorm := fresh in pose proof ((b6 0 0 0)) as Hnorm; repeat rewrite wim00 in Hnorm; repeat rewrite wim00; exact Hnorm) : T 0))). Qed.

Lemma b9 (v0 v1 : nat) : T (wim (wim 0 v0) (wim v1 v0)).
Proof. exact ((mp (b5 v0 0 v1) (b8 (wim v0 0)))). Qed.

Lemma b10 (v0 v1 : nat) : T (wim v0 (wim (wim (wim v1 v1) v1) (wim v1 v1))).
Proof. exact ((mp (b4 0 v1 v1 v0) (b9 (wim v1 v1) (wim (wim v1 v1) v1)))). Qed.

Lemma b12 (v0 : nat) : T (wim (wim (wim v0 v0) v0) (wim v0 v0)).
Proof. exact ((mp (b10 0 v0) (dtruth h))). Qed.

Lemma b13 (v0 v1 : nat) : T (wim (wim (wim v0 v0) (wim v0 v0)) (wim v1 (wim v0 v0))).
Proof. exact ((mp (b1 (wim v0 v0) v0 v0 v1) (b12 v0))). Qed.

Lemma b14 (v0 v1 : nat) : T (wim v0 (wim (wim v1 v1) (wim v1 v1))).
Proof. exact ((mp (b13 (wim v1 v1) v0) (b13 v1 (wim v1 v1)))). Qed.

Lemma b15 (v0 : nat) : T (wim (wim v0 v0) (wim v0 v0)).
Proof. exact ((mp (b14 0 v0) (dtruth h))). Qed.

Lemma b16 (v0 v1 : nat) : T (wim v0 (wim v1 v1)).
Proof. exact ((mp (b13 v1 v0) (b15 v1))). Qed.

Lemma b17 (v0 : nat) : T (wim v0 v0).
Proof. exact ((mp (b16 0 v0) (dtruth h))). Qed.

Lemma b18 (v0 v1 v2 : nat) : T (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact ((mp (b1 v0 v1 v0 v2) (b17 (wim v0 v1)))). Qed.

Lemma b19 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact ((mp (b1 (wim v1 v2) v1 v0 v3) (b18 v1 v2 v0))). Qed.

Lemma b20 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact ((mp (b1 (wim v3 v1) (wim v1 v2) v0 v4) (b19 v3 v1 v2 v0))). Qed.

Lemma b21 (v0 v1 v2 v3 : nat) : T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact ((mp (b20 (wim v2 0) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (b5 v2 (wim (wim v1 v2) v3) v1))). Qed.

Lemma b22 (v0 v1 v2 : nat) : T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact ((mp (b21 0 v0 v1 v2) (dtruth h))). Qed.

Lemma b23 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact ((mp (b1 (wim (wim v0 v1) v2) v1 v0 v3) (b22 v0 v1 v2))). Qed.

Lemma b24 (v0 v1 v2 : nat) : T (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact ((mp (b23 (wim v1 v2) v1 v1 v0) (b18 v1 v2 (wim (wim v1 v2) v1)))). Qed.

Lemma b25 (v0 v1 : nat) : T (wim (wim (wim v0 v1) v0) v0).
Proof. exact ((mp (b24 0 v0 v1) (dtruth h))). Qed.

Lemma b26 (v0 v1 v2 : nat) : T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact ((mp (b0 (wim v0 v1) v0 v2) (b25 v0 v1))). Qed.

Lemma b27 (v0 v1 v2 : nat) : T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact ((mp (b26 (wim v1 (wim v1 v2)) (wim v1 v2) v0) (b26 v1 v2 (wim v1 (wim v1 v2))))). Qed.

Lemma b28 (v0 v1 : nat) : T (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact ((mp (b27 0 v0 v1) (dtruth h))). Qed.

Lemma b29 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact ((mp (b1 v1 (wim v1 v2) v0 v3) (b26 v1 v2 v0))). Qed.

Lemma b30 (v0 v1 v2 : nat) : T (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim v1 v2)) v1) v1) (b29 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))). Qed.

Lemma b31 (v0 v1 v2 v3 v4 v5 : nat) : T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))).
Proof. exact ((drho8 h (wim (wim (wim v2 v1) v3) v4) v5 v0 v1 (le_l v4 (le_l v3 (le_r v2 (Nat.le_refl _)))))). Qed.

Lemma b33 (v0 v1 v2 v3 : nat) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact ((mp (b0 (wim v1 (wim v0 v2)) v0 v3) (b30 v1 v0 v2))). Qed.

Lemma b35 (v0 v1 v2 : nat) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))).
Proof. exact ((mp (b28 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (b33 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))). Qed.

Lemma b36 (v0 v1 v2 v3 v4 v5 : nat) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact ((mp (b1 (wim v3 (wim v2 v4)) (wim v1 v2) v0 v5) (b20 v3 v2 v4 v1 v0))). Qed.

Lemma b37 (v0 v1 : nat) : T (wim (wim v0 v1) (wim (wim (wim v1 v0) v0) v1)).
Proof. exact ((mp (b35 (wim (wim v1 v0) v0) (wim v0 v1) v1) (b0 v1 v0 (wim (wim v1 v0) v0)))). Qed.

Lemma b38 (v0 v1 v2 v3 : nat) : T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact ((mp (b36 (wim v3 v1) v1 v2 (wim (wim v1 v2) v3) v3 v0) (b2 v3 v1 v2 v2))). Qed.

Lemma b39 (v0 v1 v2 : nat) : T (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact ((mp (b38 0 v0 v1 v2) (ltac:(let Hnorm := fresh in pose proof ((b38 0 0 0 0)) as Hnorm; repeat rewrite wim00 in Hnorm; repeat rewrite wim00; exact Hnorm) : T 0))). Qed.

Lemma b40 (v0 v1 v2 : nat) : T (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ((mp (b39 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (b0 v1 v0 v2))). Qed.

Lemma b41 (v0 v1 v2 v3 : nat) : T (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))).
Proof. exact ((mp (b39 v1 v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) (b40 (wim v1 v0) v2 v3))). Qed.

Lemma b42 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact ((mp (b31 v0 v1 v0 v2 (wim v3 v2) v4) (b40 (wim v0 v1) v2 v3))). Qed.

Lemma b43 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) (wim v4 v3)).
Proof. exact ((mp (b40 (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3 v4) (b18 v0 v1 v2))). Qed.

Lemma b44 (v0 v1 v2 v3 : nat) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact ((mp (b28 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (b42 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))). Qed.

Lemma b45 (v0 v1 v2 v3 v4 : nat) : T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact ((mp (b0 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 v4) (b44 v0 v1 v2 v3))). Qed.

Lemma b46 (v0 v1 v2 : nat) : T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v0) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ((mp (b37 v0 (wim (wim v0 v1) (wim v2 v1))) (b40 v0 v1 v2))). Qed.

Lemma b47 (v0 v1 v2 v3 v4 v5 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) (wim v5 v4)).
Proof. exact ((mp (b40 (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4 v5) (b41 v0 v1 v2 v3))). Qed.

Lemma b48 (v0 v1 v2 v3 : nat) : T (wim (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) v3).
Proof. exact ((mp (b28 (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3) v3) (b43 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v0) (wim v2 v0)) v3)))). Qed.

Lemma b49 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) v4).
Proof. exact ((mp (b28 (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4) v4) (b47 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) v4)))). Qed.

Lemma b50 (v0 v1 v2 v3 v4 v5 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact ((mp (b1 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) v0 v5) (b45 v1 v2 v3 v4 v0))). Qed.

Lemma b51 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (b50 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))). Qed.

Lemma b52 (v0 v1 v2 v3 : nat) : T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact ((mp (b46 v0 (wim v1 v2) (wim (wim v0 v3) v2)) (b51 (wim v0 (wim v1 v2)) v0 v3 v2 v1))). Qed.

Lemma b53 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3))).
Proof. exact ((mp (b49 v0 v4 v3 v2 (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3)))) (b52 v0 (wim (wim v4 v0) v3) (wim v2 v3) v1))). Qed.

Lemma b54 (v0 v1 v2 v3 : nat) : T (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0)).
Proof. exact ((mp (b48 v0 v1 v3 (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0))) (b52 (wim (wim v0 v1) v0) v3 v0 v2))). Qed.

Lemma b55 (v0 v1 v2 v3 v4 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) (wim v4 v1)).
Proof. exact ((mp (b53 (wim (wim (wim v1 v2) v1) v3) v1 v4 v1 v0) (b54 v1 v2 v3 v4))). Qed.

Lemma b56 (v0 v1 v2 v3 : nat) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) (b55 v0 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1)))). Qed.

Lemma b57 (v0 v1 v2 : nat) : T (wim (wim v0 v1) (wim (wim (wim v0 v2) v0) v1)).
Proof. exact ((mp (b46 v0 v1 (wim (wim v0 v2) v0)) (b56 (wim v0 v1) v0 v2 v1))). Qed.

Lemma b58 (v0 v1 v2 : nat) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 (wim v0 v1))) (wim v2 (wim v1 (wim v0 v1)))).
Proof. exact ((mp (b1 (wim v1 (wim v0 v1)) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b0 v1 (wim v0 v1) v0))). Qed.

Lemma b59 (v0 v1 v2 : nat) : T (wim v0 (wim v1 (wim v2 v1))).
Proof. exact ((mp (b58 v2 v1 v0) (b18 (wim v2 v1) v1 v1))). Qed.

Lemma b60 (v0 v1 : nat) : T (wim v0 (wim v1 v0)).
Proof. exact ((mp (b59 0 v0 v1) (dtruth h))). Qed.

Lemma basisK (a b : nat) : T (wim a (wim b a)).
Proof. exact (b60 a b). Qed.

Lemma basisJ (a b c : nat) : T (wim (wim a b) (wim (wim (wim a c) a) b)).
Proof. exact (b57 a b c). Qed.

Lemma cd0 (v0 v1 v2 v3 : nat) (hb0 : v1 <= v2) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))).
Proof. exact ((drho8 h v2 v3 v0 v1 hb0)). Qed.

Lemma cd29 (v0 v1 v2 : nat)  :
    T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v1 v2)).
Proof. exact ((mp (b28 (wim (wim v0 v1) (wim v1 v2)) (wim v1 v2)) (b19 v0 v1 v2 (wim (wim v0 v1) (wim v1 v2))))). Qed.

Lemma cd30 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v3 (wim v2 v0))).
Proof. exact ((mp (cd0 (wim v2 v0) (wim v0 v1) (wim v0 v1) v3 (Nat.le_refl _)) (cd29 v2 v0 v1))). Qed.

Lemma cd31 (v0 v1 v2 : nat)  :
    T (wim v0 (wim v1 (wim v2 v0))).
Proof. exact ((mp (b22 v0 (wim v1 (wim v2 v0)) (wim v2 v0)) (cd30 v0 (wim v1 (wim v2 v0)) v2 v1))). Qed.

Lemma cd32 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) (wim v4 v2)).
Proof. exact ((mp (cd0 v2 v3 (wim v0 (wim v1 (wim v2 v3))) v4 (le_r v0 (le_r v1 (le_r v2 (Nat.le_refl _))))) (cd31 (wim v2 v3) v0 v1))). Qed.

Lemma cd33 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2).
Proof. exact ((mp (b28 (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2) (cd32 v0 v1 v2 v3 (wim (wim v0 (wim v1 (wim v2 v3))) v2)))). Qed.

Lemma cd34 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v4 (wim v1 (wim v2 (wim v0 v3))))).
Proof. exact ((mp (cd0 (wim v1 (wim v2 (wim v0 v3))) v0 v0 v4 (Nat.le_refl _)) (cd33 v1 v2 v0 v3))). Qed.

Lemma cd35 (v0 v1 v2 v3 : nat)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))).
Proof. exact ((mp (b28 (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) (cd34 v0 v1 v2 v3 (wim v0 (wim v1 (wim v2 (wim v0 v3))))))). Qed.

Lemma cd46 (v0 v1 v2 v3 : nat) (hb0 : v3 <= v1) :
    T (wim v0 (wim (wim v1 v2) (wim (wim (wim v2 v3) v1) v2))).
Proof. exact ((mp (b33 (wim (wim v2 v3) v1) (wim v1 v2) v2 v0) (cd0 v2 v3 v1 (wim (wim v2 v3) v1) hb0))). Qed.

Lemma cd47 (v0 v1 v2 : nat) (hb0 : v2 <= v0) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact ((mp (cd46 0 v0 v1 v2 hb0) (ltac:(let Hnorm := fresh in pose proof ((cd0 0 0 0 0 (Nat.le_0_l _))) as Hnorm; repeat rewrite wim00 in Hnorm; repeat rewrite wim00; exact Hnorm) : T 0))). Qed.

Lemma cd52 (v0 v1 v2 v3 : nat) (hb0 : v3 <= v0) :
    T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ((mp (cd47 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (b40 v0 v1 v2))). Qed.

Lemma cd54 (v0 v1 v2 v3 v4 : nat) (hb0 : v2 <= (wim (wim v3 (wim v1 v4)) v1)) :
    T (wim (wim (wim (wim v0 v1) v2) (wim (wim v3 (wim v1 v4)) v1)) (wim v0 v1)).
Proof. exact ((mp (cd47 (wim (wim v3 (wim v1 v4)) v1) (wim v0 v1) v2 hb0) (b29 v3 v1 v4 v0))). Qed.

Lemma cd60 (v0 v1 v2 v3 : nat) (hb0 : v3 <= (wim v1 (wim v1 v2))) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact ((mp (cd47 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (b26 v1 v2 v0))). Qed.

Lemma cd61 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) (wim v3 v2))).
Proof. exact ((mp (b57 v0 (wim (wim v0 v2) (wim v3 v2)) v1) (b40 v0 v2 v3))). Qed.

Lemma cd62 (v0 v1 : nat)  :
    T (wim v0 (wim (wim v0 v1) v1)).
Proof. exact ((mp (cd60 v0 (wim v0 v1) v1 v0 (le_l (wim (wim v0 v1) v1) (le_l v1 (Nat.le_refl _)))) (cd61 v0 (wim (wim v0 v1) v1) v1 (wim v0 v1)))). Qed.

Lemma cd63 (v0 v1 v2 : nat)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) v2)).
Proof. exact ((mp (b57 v0 (wim (wim v0 v2) v2) v1) (cd62 v0 v2))). Qed.

Lemma cd64 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))).
Proof. exact ((mp (cd0 (wim v0 v2) v0 (wim (wim v0 v1) v1) v3 (le_l v1 (le_l v1 (Nat.le_refl _)))) (cd63 v0 v2 v1))). Qed.

Lemma cd65 (v0 v1 v2 : nat)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)).
Proof. exact ((mp (b28 (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) (cd64 v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2))))). Qed.

Lemma cd66 (v0 v1 v2 v3 : nat) (hb0 : v3 <= v2) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))).
Proof. exact ((mp (cd47 v2 (wim v0 (wim v1 v2)) v3 hb0) (cd31 v2 v0 v1))). Qed.

Lemma cd67 (v0 v1 v2 v3 : nat)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))).
Proof. exact ((mp (cd66 v0 v1 (wim (wim v0 v2) (wim v3 v2)) v0 (le_l (wim v3 v2) (le_l v2 (Nat.le_refl _)))) (cd61 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v2 v3))). Qed.

Lemma cd68 (v0 v1 v2 v3 : nat)  :
    T (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))).
Proof. exact ((mp (cd65 v0 v1 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) (cd67 (wim (wim v0 v1) v1) v0 v2 v3))). Qed.

Lemma cd69 (v0 v1 v2 : nat)  :
    T (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)).
Proof. exact ((mp (b35 v0 (wim (wim (wim v0 v1) v1) v2) v2) (cd68 v0 v1 v2 v0))). Qed.

Lemma cd70 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v4 (wim v2 (wim v1 v3)))).
Proof. exact ((mp (cd0 (wim v2 (wim v1 v3)) v1 (wim v0 v1) v4 (le_r v0 (Nat.le_refl _))) (b29 v2 v1 v3 v0))). Qed.

Lemma cd71 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v2 (wim v1 v3))).
Proof. exact ((mp (b28 (wim (wim v0 v1) (wim v2 (wim v1 v3))) (wim v2 (wim v1 v3))) (cd70 v0 v1 v2 v3 (wim (wim v0 v1) (wim v2 (wim v1 v3)))))). Qed.

Lemma cd72 (v0 v1 v2 v3 v4 : nat)  :
    T (wim v0 (wim v1 (wim (wim (wim v2 v0) v3) (wim v4 v3)))).
Proof. exact ((mp (b39 v2 v0 (wim v1 (wim (wim (wim v2 v0) v3) (wim v4 v3)))) (cd67 (wim v2 v0) v1 v3 v4))). Qed.

Lemma cd73 (v0 v1 v2 v3 v4 : nat)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) (wim v4 v3))).
Proof. exact ((mp (cd65 v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) (wim v4 v3))) (cd72 (wim (wim v0 v2) v2) v0 v1 v3 v4))). Qed.

Lemma cd74 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v4) (wim v2 v4)).
Proof. exact ((mp (cd71 v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v4) v4) (cd73 (wim v1 v2) v0 v3 v4 v2))). Qed.

Lemma cd75 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact ((mp (cd52 (wim v0 v1) v2 (wim (wim v3 v0) v2) v1 (le_r v0 (Nat.le_refl _))) (cd74 (wim (wim v0 v1) v2) v3 v0 v2 v1))). Qed.

Lemma cd76 (v0 v1 v2 : nat) (hb0 : v2 <= v0) :
    T (wim (wim (wim (wim (wim v0 v1) v1) v2) v0) (wim (wim v0 v1) v1)).
Proof. exact ((mp (cd47 v0 (wim (wim v0 v1) v1) v2 hb0) (cd62 v0 v1))). Qed.

Lemma cd77 (v0 v1 v2 : nat)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)).
Proof. exact ((mp (b28 (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) (cd30 v0 v1 v2 (wim (wim v0 v1) (wim v2 v0))))). Qed.

Lemma cd78 (v0 v1 v2 : nat)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) v2))).
Proof. exact ((mp (cd66 v0 v1 (wim (wim v0 v2) v2) v0 (le_l v2 (le_l v2 (Nat.le_refl _)))) (cd63 v0 (wim v1 (wim (wim v0 v2) v2)) v2))). Qed.

Lemma cd79 (v0 v1 v2 v3 : nat)  :
    T (wim v0 (wim v1 (wim (wim (wim v2 v0) v3) v3))).
Proof. exact ((mp (b39 v2 v0 (wim v1 (wim (wim (wim v2 v0) v3) v3))) (cd78 (wim v2 v0) v1 v3))). Qed.

Lemma cd80 (v0 v1 v2 v3 : nat)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)).
Proof. exact ((mp (cd65 v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) (cd79 (wim (wim v0 v2) v2) v0 v1 v3))). Qed.

Lemma cd81 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1) v1).
Proof. exact ((mp (cd77 v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1)) (cd80 (wim v1 v2) v0 v3 v1))). Qed.

Lemma cd82 (v0 v1 v2 : nat)  :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact ((mp (cd76 v0 (wim (wim (wim v0 v1) v2) v2) v0 (Nat.le_refl _)) (cd81 (wim v0 (wim (wim (wim v0 v1) v2) v2)) v0 v1 v2))). Qed.

Lemma cd83 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)).
Proof. exact ((mp (b28 (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) (b20 v0 v1 v2 v3 (wim (wim v0 (wim v1 v2)) (wim v3 v1))))). Qed.

Lemma cd84 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2) v2).
Proof. exact ((mp (cd83 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2)) (cd80 (wim v1 (wim v2 v3)) v0 v4 v2))). Qed.

Lemma cd85 (v0 v1 v2 v3 : nat)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact ((mp (cd52 v0 v1 (wim (wim v2 (wim v0 v3)) v1) v0 (Nat.le_refl _)) (cd84 (wim v0 v1) v2 v0 v3 v1))). Qed.

Lemma cd86 (v0 v1 v2 : nat)  :
    T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact ((mp (cd82 (wim v0 v1) (wim v0 v2) v1) (cd85 v0 v1 (wim v0 v1) v2))). Qed.

Lemma cd87 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact ((mp (cd75 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (cd86 v1 v2 v3))). Qed.

Lemma cd88 (v0 v1 v2 : nat)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact ((mp (cd52 v0 (wim v1 v2) (wim v1 v0) v0 (Nat.le_refl _)) (cd87 (wim v0 (wim v1 v2)) v1 v0 v2))). Qed.

Lemma cd89 (v0 v1 v2 v3 : nat)  :
    T (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact ((mp (cd88 v1 v0 (wim (wim v1 v2) (wim v3 v2))) (cd67 v1 v0 v2 v3))). Qed.

Lemma cd90 (v0 v1 v2 v3 : nat)  :
    T (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact ((mp (cd69 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (cd89 (wim v0 v1) v1 v2 v3))). Qed.

Lemma cd91 (v0 v1 v2 : nat)  :
    T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))).
Proof. exact ((mp (cd35 v0 (wim v0 v1) (wim v1 v2) v2) (cd90 v0 v1 v2 v0))). Qed.

Lemma cd92 (v0 v1 v2 : nat)  :
    T (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact ((mp (b39 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (cd62 (wim v1 v0) v2))). Qed.

Lemma cd93 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) (wim v4 v1)).
Proof. exact ((mp (cd0 v1 v2 (wim (wim (wim v0 (wim v1 v2)) v3) v3) v4 (le_l v3 (le_l v3 (le_r v0 (le_r v1 (Nat.le_refl _)))))) (cd92 (wim v1 v2) v0 v3))). Qed.

Lemma cd94 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1).
Proof. exact ((mp (b28 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1) v1) (cd93 v0 v1 v2 v3 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v3) v1)))). Qed.

Lemma cd95 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v2) v4)) v2) v2).
Proof. exact ((mp (cd54 (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v2) v4)) v2) v2 (wim (wim v1 (wim v2 v3)) v2) v1 v3 (Nat.le_refl _)) (cd94 v0 (wim (wim v1 (wim v2 v3)) v2) v4 v2))). Qed.

Lemma cd96 (v0 v1 v2 v3 : nat)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v0) v1)).
Proof. exact ((mp (cd52 v0 v1 (wim (wim v2 (wim v0 v3)) v0) v0 (Nat.le_refl _)) (cd95 (wim v0 v1) v2 v0 v3 v1))). Qed.

Lemma cd97 (v0 v1 v2 v3 v4 : nat)  :
    T (wim (wim (wim v0 (wim v1 v2)) v1) (wim (wim v1 v3) (wim v4 v3))).
Proof. exact ((mp (cd96 v1 (wim (wim v1 v3) (wim v4 v3)) v0 v2) (b40 v1 v3 v4))). Qed.

Lemma cd98 (v0 v1 v2 v3 : nat)  :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim v0 v3)).
Proof. exact ((mp (cd52 (wim (wim v0 v1) (wim v2 v1)) v3 v0 v0 (le_l (wim v2 v1) (le_l v1 (Nat.le_refl _)))) (cd97 (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0 v3 v1 v2))). Qed.

Lemma cd99 (v0 v1 v2 : nat)  :
    T (wim (wim v0 v1) (wim v0 (wim v2 v1))).
Proof. exact ((mp (cd98 (wim v0 v1) v1 v2 (wim v0 (wim v2 v1))) (cd69 v0 v1 (wim v2 v1)))). Qed.


Lemma composition (a b c : nat) :
  T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (cd91 a b c). Qed.

Lemma lift_right {a b : nat} (hab : T (wim a b)) (x : nat) :
  T (wim (wim x a) (wim x b)).
Proof. exact (mp (cd88 a x b) (mp (cd99 a b x) hab)). Qed.

Lemma rho8_all (a b c u : nat) : T (rho8 a b c u).
Proof.
  pose proof (mp (basisJ c (wim b c) u) (basisK c b)) as hqd.
  exact (mp (lift_right (lift_right hqd (wim a c))
             (wim (wim c u) a)) (composition (wim c u) a c)).
Qed.
End Proof.
End Direct.

(** The original public interface remains unchanged. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u :
  T (rho8 a b c u).
Proof. exact (Direct.rho8_all T h a b c u). Qed.
Print Assumptions rho8_all.
