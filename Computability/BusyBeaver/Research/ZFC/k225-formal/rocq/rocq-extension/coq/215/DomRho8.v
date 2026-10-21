(** Dominated rho8 derives every rho8 instance.

    [rho8 a b c u] is Lukasiewicz's single axiom ((c -> u) -> a) -> ((a -> c) -> (b -> c));
    [DomImp] grants it only when [u <= a]. The 52 lemmas are the condensed-detachment
    derivation of k225-formal/rho8cd/derivation.txt, rendered by generate_domrho8_cd.py
    exactly as for the Lean DomRho8 (the search that found it is untrusted). *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Lemma le_l {u x} y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y} x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

Section Derivation.
Variable T : nat -> Prop.
Variable h : DomImp T.
Local Opaque wim.

Lemma d1 v0 v1 v2 v3 v4 (hb0 : v3 <= v0) :
  T (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))).
Proof. exact (dmp h _ _ (drho8 h (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0 (le_l (wim v2 v1) (le_l v1 (le_n _)))) (drho8 h v0 v2 v1 v3 hb0)). Qed.

Lemma d2 v0 v1 v2 v3 v4 v5 (hb0 : v2 <= v3) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))).
Proof. exact (dmp h _ _ (drho8 h (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2) (le_r v0 (le_n _))) (d1 v3 v1 v4 v2 v0 hb0)). Qed.

Lemma d3 v0 v1 v2 v3 :
  T (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))).
Proof. exact (dmp h _ _ (d2 (wim v1 0) v1 v2 (wim v1 v2) v3 v0 (le_r v1 (le_n _))) (drho8 h (wim v1 v2) v3 v1 0 (Nat.le_0_l _))). Qed.

Lemma d4 v0 v1 v2 :
  T (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact (dmp h _ _ (d3 0 v0 v1 v2) (dtruth h)). Qed.

Lemma d5 v0 v1 v2 v3 :
  T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact (dmp h _ _ (drho8 h (wim v0 v1) v3 (wim v1 v2) v1 (le_r v0 (le_n _))) (d4 v1 v2 v0)). Qed.

Lemma d6 v0 v1 v2 v3 v4 :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact (dmp h _ _ (drho8 h (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2) (le_r v0 (le_n _))) (d5 v3 v1 v2 v0)). Qed.

Lemma d7 v0 v1 v2 v3 :
  T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact (dmp h _ _ (d6 (wim v2 0) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (drho8 h (wim (wim v1 v2) v3) v1 v2 0 (Nat.le_0_l _))). Qed.

Lemma d8 v0 v1 v2 v3 v4 v5 :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact (dmp h _ _ (drho8 h (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2) (le_r v0 (le_n _))) (d6 v3 v2 v4 v1 v0)). Qed.

Lemma d9 v0 v1 v2 :
  T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact (dmp h _ _ (d7 0 v0 v1 v2) (dtruth h)). Qed.

Lemma d10 v0 v1 v2 v3 :
  T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact (dmp h _ _ (d8 (wim v3 0) v1 v2 (wim (wim v1 v2) v3) v3 v0) (drho8 h (wim v1 v2) v2 v3 0 (Nat.le_0_l _))). Qed.

Lemma d11 v0 v1 v2 v3 :
  T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact (dmp h _ _ (drho8 h (wim v0 v1) v3 (wim (wim v0 v1) v2) v1 (le_r v0 (le_n _))) (d9 v0 v1 v2)). Qed.

Lemma d12 v0 v1 :
  T (wim v0 (wim v1 v0)).
Proof. exact (dmp h _ _ (d9 v0 (wim v1 v0) v0) (d4 v0 (wim v1 v0) v1)). Qed.

Lemma d13 v0 v1 v2 :
  T (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact (dmp h _ _ (d10 0 v0 v1 v2) (dtruth h)). Qed.

Lemma d14 v0 v1 v2 :
  T (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact (dmp h _ _ (d11 (wim v1 v2) v1 v1 v0) (d4 v1 v2 (wim (wim v1 v2) v1))). Qed.

Lemma d15 v0 v1 v2 v3 :
  T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact (dmp h _ _ (drho8 h (wim v0 (wim v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (le_n _)))) (d12 (wim v1 v2) v0)). Qed.

Lemma d16 v0 v1 v2 :
  T (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (dmp h _ _ (d13 (wim v1 0) v0 (wim (wim v0 v1) (wim v2 v1))) (drho8 h v0 v2 v1 0 (Nat.le_0_l _))). Qed.

Lemma d17 v0 v1 v2 :
  T (wim v0 (wim v1 (wim v2 v0))).
Proof. exact (dmp h _ _ (d13 v2 v0 (wim v1 (wim v2 v0))) (d12 (wim v2 v0) v1)). Qed.

Lemma d18 v0 v1 :
  T (wim (wim (wim v0 v1) v0) v0).
Proof. exact (dmp h _ _ (d14 0 v0 v1) (dtruth h)). Qed.

Lemma d19 v0 v1 v2 v3 v4 :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact (dmp h _ _ (drho8 h (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1 (le_l (wim v3 v2) (le_l v2 (le_r v0 (le_n _))))) (d16 (wim v0 v1) v2 v3)). Qed.

Lemma d20 v0 v1 v2 :
  T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact (dmp h _ _ (drho8 h v0 v2 (wim v0 v1) v0 (le_n _)) (d18 v0 v1)). Qed.

Lemma d21 v0 v1 v2 :
  T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact (dmp h _ _ (d11 v1 (wim v1 v2) (wim v1 v2) v0) (d20 v1 v2 (wim v1 (wim v1 v2)))). Qed.

Lemma d22 v0 v1 :
  T (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact (dmp h _ _ (d21 0 v0 v1) (dtruth h)). Qed.

Lemma d23 v0 v1 v2 :
  T (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact (dmp h _ _ (d22 (wim (wim v0 (wim v1 v2)) v1) v1) (d15 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1))). Qed.

Lemma d24 v0 v1 v2 v3 :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact (dmp h _ _ (d22 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (d19 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0))). Qed.

Lemma d25 v0 v1 v2 v3 :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact (dmp h _ _ (drho8 h v0 v3 (wim v1 (wim v0 v2)) v0 (le_n _)) (d23 v1 v0 v2)). Qed.

Lemma d26 v0 v1 v2 v3 v4 :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact (dmp h _ _ (drho8 h v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 (le_n _)) (d24 v0 v1 v2 v3)). Qed.

Lemma d27 v0 v1 v2 :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))).
Proof. exact (dmp h _ _ (d22 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (d25 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2))))). Qed.

Lemma d28 v0 v1 v2 v3 v4 v5 :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact (dmp h _ _ (drho8 h (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) (le_r v0 (le_n _))) (d26 v1 v2 v3 v4 v0)). Qed.

Lemma d29 v0 v1 v2 v3 v4 :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact (dmp h _ _ (d22 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (d28 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1))). Qed.

Lemma d30 v0 v1 v2 (hb0 : v2 <= v0) :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (dmp h _ _ (d27 (wim (wim v1 v2) v0) (wim v0 v1) v1) (drho8 h v0 (wim (wim v1 v2) v0) v1 v2 hb0)). Qed.

Lemma d31 v0 v1 v2 v3 (hb0 : v3 <= v0) :
  T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (dmp h _ _ (d30 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (d16 v0 v1 v2)). Qed.

Lemma d32 v0 v1 v2 v3 :
  T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact (dmp h _ _ (d31 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (le_n _)) (d29 (wim v0 (wim v1 v2)) v0 v3 v2 v1)). Qed.

Lemma d33 v0 v1 v2 v3 :
  T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))).
Proof. exact (dmp h _ _ (d32 v0 (wim v0 v3) (wim v2 v3) v1) (d16 v0 v3 v2)). Qed.

Lemma d34 v0 v1 v2 v3 (hb0 : v3 <= wim v1 (wim v1 v2)) :
  T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact (dmp h _ _ (d30 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (d20 v1 v2 v0)). Qed.

Lemma d35 v0 v1 :
  T (wim v0 (wim (wim v0 v1) v1)).
Proof. exact (dmp h _ _ (d34 v0 (wim v0 v1) v1 (wim (wim v0 v1) v1) (le_r (wim v0 v1) (le_n _))) (d33 v0 (wim (wim v0 v1) v1) (wim v0 v1) v1)). Qed.

Lemma d36 v0 v1 v2 :
  T (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact (dmp h _ _ (d13 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (d35 (wim v1 v0) v2)). Qed.

Lemma d37 v0 v1 v2 :
  T (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)).
Proof. exact (dmp h _ _ (d32 v0 (wim v0 v2) v2 v1) (d35 v0 v2)). Qed.

Lemma d38 v0 v1 v2 v3 :
  T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact (dmp h _ _ (d32 v0 (wim (wim v3 v0) v2) v2 v1) (d36 v0 v3 v2)). Qed.

Lemma d39 v0 v1 v2 v3 :
  T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact (dmp h _ _ (d33 v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1) (d36 (wim v0 v3) v2 v1)). Qed.

Lemma d40 v0 v1 v2 :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact (dmp h _ _ (d37 v0 v1 (wim (wim (wim v0 v1) v2) v2)) (d35 (wim v0 v1) v2)). Qed.

Lemma d41 v0 v1 v2 :
  T (wim (wim (wim (wim (wim v0 v1) v2) v0) v2) v2).
Proof. exact (dmp h _ _ (d40 (wim (wim v0 v1) v2) v0 v2) (d38 v0 v1 v2 (wim (wim v0 v1) v2))). Qed.

Lemma d42 v0 v1 v2 :
  T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact (dmp h _ _ (d40 (wim v0 v1) (wim v0 v2) v1) (d39 v0 v1 (wim v0 v1) v2)). Qed.

Lemma d43 v0 v1 v2 v3 :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v1)) v3) v3).
Proof. exact (dmp h _ _ (d38 (wim (wim (wim v1 v2) v3) v1) v3 v3 v0) (d41 v1 v2 v3)). Qed.

Lemma d44 v0 v1 v2 v3 :
  T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact (dmp h _ _ (d38 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (d42 v1 v2 v3)). Qed.

Lemma d45 v0 v1 v2 :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (dmp h _ _ (d31 v0 v1 (wim (wim v1 v2) v0) v0 (le_n _)) (d43 (wim v0 v1) v1 v2 v0)). Qed.

Lemma d46 v0 v1 v2 :
  T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact (dmp h _ _ (d31 v0 (wim v1 v2) (wim v1 v0) v0 (le_n _)) (d44 (wim v0 (wim v1 v2)) v1 v0 v2)). Qed.

Lemma d47 v0 v1 v2 :
  T (wim (wim v0 v1) (wim v0 (wim v2 v1))).
Proof. exact (dmp h _ _ (d46 v1 v0 (wim v2 v1)) (d17 v1 v0 v2)). Qed.

Lemma d48 v0 v1 v2 v3 :
  T (wim (wim v0 v1) (wim v2 (wim v0 (wim v3 v1)))).
Proof. exact (dmp h _ _ (d47 (wim v0 v1) (wim v0 (wim v3 v1)) v2) (d47 v0 v1 v3)). Qed.

Lemma d49 v0 v1 v2 v3 :
  T (wim (wim v0 (wim v1 v2)) (wim v0 (wim v1 (wim v3 v2)))).
Proof. exact (dmp h _ _ (d46 (wim v1 v2) v0 (wim v1 (wim v3 v2))) (d48 v1 v2 v0 v3)). Qed.

Lemma d50 v0 v1 v2 v3 :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) (wim v3 v1))).
Proof. exact (dmp h _ _ (d49 (wim v0 v1) (wim (wim v1 v2) v0) v1 v3) (d45 v0 v1 v2)). Qed.

Lemma d51 v0 v1 v2 :
  T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) v0)).
Proof. exact (dmp h _ _ (d27 (wim v2 v0) (wim (wim v0 v1) v2) v0) (d50 v2 v0 v1 (wim v2 v0))). Qed.

Lemma d52 v0 v1 v2 v3 :
  T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))).
Proof. exact (dmp h _ _ (d49 (wim (wim v0 v1) v2) (wim v2 v0) v0 v3) (d51 v0 v1 v2)). Qed.

(** Every rho8 instance follows from the dominated ones. *)
Theorem rho8_all a b c u : T (rho8 a b c u).
Proof. exact (d52 c u a b). Qed.

End Derivation.
Print Assumptions rho8_all.
