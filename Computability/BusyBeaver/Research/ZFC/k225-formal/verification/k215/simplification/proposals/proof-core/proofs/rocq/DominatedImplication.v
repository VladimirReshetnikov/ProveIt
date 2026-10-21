(* Representation-independent dominated implication, direct proof-term port.
   Based on ProveIt aa66d0a33f1f8237a348899eb8095b045a502832 DomRho8,
   with the thirteen checked condensed-detachment shortcuts of this packet.
   The carrier need not encode formulas injectively. No truth constant,
   bottom element, transitivity, formula decoder, or zero-collapse axiom is used.
   Proof terms below are kernel checked; the translator is untrusted. *)

Module DominatedImplication.
Section Generic.
Context {A : Type}.
Variables (wim : A -> A -> A) (below : A -> A -> Prop).
Hypothesis below_refl : forall a, below a a.
Hypothesis grow_left : forall u x y, below u x -> below u (wim x y).
Hypothesis grow_right : forall u y x, below u y -> below u (wim x y).
Local Infix "≼" := below (at level 50).
Definition rho8 (a b c u : A) : A :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c)).
Variable T : A -> Prop.
Hypothesis mp : forall {a b}, T (wim a b) -> T a -> T b.
Hypothesis row : forall a b c u, below u a -> T (rho8 a b c u).
Local Definition le_l {u x : A} (y : A) (h : u ≼ x) : u ≼ wim x y :=
  grow_left u x y h.
Local Definition le_r {u y : A} (x : A) (h : u ≼ y) : u ≼ wim x y :=
  grow_right u y x h.

Section Seed.
Variable tau : A.
Hypothesis seed : T tau.

Lemma b1 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim v2 v1)) (wim (wim (wim v2 v1) v0) (wim v3 v0))).
Proof. exact (row (wim v2 v1) v3 v0 v1 (le_r v2 (below_refl _))). Qed.

Lemma b3 (v0 v1 v2 : A) : T (wim (wim (wim (wim (wim v0 v1) v1) (wim v0 v1)) (wim v1 v1)) (wim v2 (wim v1 v1))).
Proof. exact ((mp (b1 (wim v1 v1) (wim v0 v1) (wim (wim v0 v1) v1) v2) (b1 v1 v1 v0 v0))). Qed.

Lemma b4 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim v1 v1)) (wim (wim (wim v2 v1) v1) (wim v2 v1))) (wim v3 (wim (wim (wim v2 v1) v1) (wim v2 v1)))).
Proof. exact ((mp (b1 (wim (wim (wim v2 v1) v1) (wim v2 v1)) (wim v1 v1) v0 v3) (b3 v2 v1 v0))). Qed.

Lemma b10 (v0 v1 : A) : T (wim v0 (wim (wim (wim v1 v1) v1) (wim v1 v1))).
Proof. exact ((mp (b4 (wim v1 v1) v1 v1 v0) (b1 v1 v1 v1 v1))). Qed.

Lemma b12 (v0 : A) : T (wim (wim (wim v0 v0) v0) (wim v0 v0)).
Proof. exact ((mp (b10 tau v0) seed)). Qed.

Lemma b13 (v0 v1 : A) : T (wim (wim (wim v0 v0) (wim v0 v0)) (wim v1 (wim v0 v0))).
Proof. exact ((mp (b1 (wim v0 v0) v0 v0 v1) (b12 v0))). Qed.

Lemma b14 (v0 v1 : A) : T (wim v0 (wim (wim v1 v1) (wim v1 v1))).
Proof. exact ((mp (b13 (wim v1 v1) v0) (b13 v1 (wim v1 v1)))). Qed.

Lemma b15 (v0 : A) : T (wim (wim v0 v0) (wim v0 v0)).
Proof. exact ((mp (b14 tau v0) seed)). Qed.

Lemma b16 (v0 v1 : A) : T (wim v0 (wim v1 v1)).
Proof. exact ((mp (b13 v1 v0) (b15 v1))). Qed.

Lemma b17 (v0 : A) : T (wim v0 v0).
Proof. exact ((mp (b16 tau v0) seed)). Qed.

Lemma b18 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact ((mp (b1 v0 v1 v0 v2) (b17 (wim v0 v1)))). Qed.

Lemma b31 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 v1) (wim (wim (wim v2 v1) v3) v4)) (wim (wim (wim (wim (wim v2 v1) v3) v4) v0) (wim v5 v0))).
Proof. exact (row (wim (wim (wim v2 v1) v3) v4) v5 v0 v1 (le_l v4 (le_l v3 (le_r v2 (below_refl _))))). Qed.

Lemma b19 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact ((mp (b1 (wim v1 v2) v1 v0 v3) (b18 v1 v2 v0))). Qed.

Lemma b20 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact ((mp (b1 (wim v3 v1) (wim v1 v2) v0 v4) (b19 v3 v1 v2 v0))). Qed.

Lemma b36 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact ((mp (b1 (wim v3 (wim v2 v4)) (wim v1 v2) v0 v5) (b20 v3 v2 v4 v1 v0))). Qed.

Lemma b38 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact ((mp (b36 (wim v3 v2) v1 v2 (wim (wim v1 v2) v3) v3 v0) (b1 v3 v2 v1 v2))). Qed.

Lemma b39 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact ((mp (b38 tau v0 v1 v2) seed)). Qed.

Lemma b0 (v0 v1 v2 : A) : T (wim (wim (wim v0 v1) v1) (wim (wim v1 v0) (wim v2 v0))).
Proof. exact (row v1 v2 v0 v1 (below_refl _)). Qed.

Lemma b40 (v0 v1 v2 : A) : T (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ((mp (b39 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (b0 v1 v0 v2))). Qed.

Lemma b42 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact ((mp (b31 v0 v1 v0 v2 (wim v3 v2) v4) (b40 (wim v0 v1) v2 v3))). Qed.

Lemma b21 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact ((mp (b18 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2)) (wim v1 v2) v0) (b42 (wim v1 v2) v3 v2 v1 (wim (wim (wim v1 v2) v3) v2)))). Qed.

Lemma b22 (v0 v1 v2 : A) : T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact ((mp (b21 tau v0 v1 v2) seed)). Qed.

Lemma b23 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact ((mp (b1 (wim (wim v0 v1) v2) v1 v0 v3) (b22 v0 v1 v2))). Qed.

Lemma b24 (v0 v1 v2 : A) : T (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact ((mp (b23 (wim v1 v2) v1 v1 v0) (b18 v1 v2 (wim (wim v1 v2) v1)))). Qed.

Lemma b25 (v0 v1 : A) : T (wim (wim (wim v0 v1) v0) v0).
Proof. exact ((mp (b24 tau v0 v1) seed)). Qed.

Lemma b60 (v0 v1 : A) : T (wim v0 (wim v1 v0)).
Proof. exact ((mp (b22 v0 (wim v1 v0) v0) (b18 v0 (wim v1 v0) v1))). Qed.

Lemma b26 (v0 v1 v2 : A) : T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact ((mp (b0 (wim v0 v1) v0 v2) (b25 v0 v1))). Qed.

Lemma b27 (v0 v1 v2 : A) : T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact ((mp (b26 (wim v1 (wim v1 v2)) (wim v1 v2) v0) (b26 v1 v2 (wim v1 (wim v1 v2))))). Qed.

Lemma b28 (v0 v1 : A) : T (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact ((mp (b27 tau v0 v1) seed)). Qed.

Lemma cd0 (v0 v1 v2 v3 : A) (hb0 : v1 ≼ v2) :
    T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))).
Proof. exact (row v2 v3 v0 v1 hb0). Qed.

Lemma b29 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact ((mp (b1 v1 (wim v1 v2) v0 v3) (b26 v1 v2 v0))). Qed.

Lemma b30 (v0 v1 v2 : A) : T (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim v1 v2)) v1) v1) (b29 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)))). Qed.

Lemma b33 (v0 v1 v2 v3 : A) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact ((mp (b0 (wim v1 (wim v0 v2)) v0 v3) (b30 v1 v0 v2))). Qed.

Lemma b35 (v0 v1 v2 : A) : T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))).
Proof. exact ((mp (b28 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (b33 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2)))))). Qed.

Lemma b37 (v0 v1 : A) : T (wim (wim v0 v1) (wim (wim (wim v1 v0) v0) v1)).
Proof. exact ((mp (b35 (wim (wim v1 v0) v0) (wim v0 v1) v1) (b0 v1 v0 (wim (wim v1 v0) v0)))). Qed.

Lemma b46 (v0 v1 v2 : A) : T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v0) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact ((mp (b37 v0 (wim (wim v0 v1) (wim v2 v1))) (b40 v0 v1 v2))). Qed.

Lemma b44 (v0 v1 v2 v3 : A) : T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact ((mp (b28 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (b42 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)))). Qed.

Lemma b45 (v0 v1 v2 v3 v4 : A) : T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact ((mp (b0 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 v4) (b44 v0 v1 v2 v3))). Qed.

Lemma b50 (v0 v1 v2 v3 v4 v5 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact ((mp (b1 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) v0 v5) (b45 v1 v2 v3 v4 v0))). Qed.

Lemma b51 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (b50 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)))). Qed.

Lemma b52 (v0 v1 v2 v3 : A) : T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact ((mp (b46 v0 (wim v1 v2) (wim (wim v0 v3) v2)) (b51 (wim v0 (wim v1 v2)) v0 v3 v2 v1))). Qed.

Lemma cd46 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ v1) :
    T (wim v0 (wim (wim v1 v2) (wim (wim (wim v2 v3) v1) v2))).
Proof. exact ((mp (b33 (wim (wim v2 v3) v1) (wim v1 v2) v2 v0) (cd0 v2 v3 v1 (wim (wim v2 v3) v1) hb0))). Qed.

Lemma cd47 (v0 v1 v2 : A) (hb0 : v2 ≼ v0) :
    T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact ((mp (cd46 tau v0 v1 v2 hb0) seed)). Qed.

Lemma cd60 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ (wim v1 (wim v1 v2))) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact ((mp (cd47 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (b26 v1 v2 v0))). Qed.

Lemma b41 (v0 v1 v2 v3 : A) : T (wim v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))).
Proof. exact ((mp (b39 v1 v0 (wim (wim (wim v1 v0) v2) (wim v3 v2))) (b40 (wim v1 v0) v2 v3))). Qed.

Lemma b53 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim (wim v4 v0) v3) (wim v2 v3))).
Proof. exact ((mp (b52 v0 (wim (wim v4 v0) v3) (wim v2 v3) v1) (b41 v0 v4 v3 v2))). Qed.

Lemma b54 (v0 v1 v2 v3 : A) : T (wim (wim (wim (wim (wim v0 v1) v0) v2) v0) (wim v3 v0)).
Proof. exact ((mp (b52 (wim (wim v0 v1) v0) v3 v0 v2) (b18 v0 v1 v3))). Qed.

Lemma b55 (v0 v1 v2 v3 v4 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) (wim v4 v1)).
Proof. exact ((mp (b53 (wim (wim (wim v1 v2) v1) v3) v1 v4 v1 v0) (b54 v1 v2 v3 v4))). Qed.

Lemma b56 (v0 v1 v2 v3 : A) : T (wim (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1).
Proof. exact ((mp (b28 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1) v1) (b55 v0 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 v2) v1) v3)) v1)))). Qed.

Lemma b57 (v0 v1 v2 : A) : T (wim (wim v0 v1) (wim (wim (wim v0 v2) v0) v1)).
Proof. exact ((mp (b46 v0 v1 (wim (wim v0 v2) v0)) (b56 (wim v0 v1) v0 v2 v1))). Qed.

Lemma cd61 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) (wim v3 v2))).
Proof. exact ((mp (b57 v0 (wim (wim v0 v2) (wim v3 v2)) v1) (b40 v0 v2 v3))). Qed.

Lemma cd62 (v0 v1 : A)  :
    T (wim v0 (wim (wim v0 v1) v1)).
Proof. exact ((mp (cd60 v0 (wim v0 v1) v1 v0 (le_l (wim (wim v0 v1) v1) (le_l v1 (below_refl _)))) (cd61 v0 (wim (wim v0 v1) v1) v1 (wim v0 v1)))). Qed.

Lemma cd92 (v0 v1 v2 : A)  :
    T (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact ((mp (b39 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (cd62 (wim v1 v0) v2))). Qed.

Lemma cd75 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact ((mp (b52 v0 (wim (wim v3 v0) v2) v2 v1) (cd92 v0 v3 v2))). Qed.

Lemma cd33 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim v1 (wim v2 v3))) v2) v2).
Proof. exact ((mp (cd75 (wim v1 (wim v2 v3)) v2 v2 v0) (b30 v1 v2 v3))). Qed.

Lemma cd34 (v0 v1 v2 v3 v4 : A)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v4 (wim v1 (wim v2 (wim v0 v3))))).
Proof. exact ((mp (cd0 (wim v1 (wim v2 (wim v0 v3))) v0 v0 v4 (below_refl _)) (cd33 v1 v2 v0 v3))). Qed.

Lemma cd35 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))).
Proof. exact ((mp (b28 (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))) (cd34 v0 v1 v2 v3 (wim v0 (wim v1 (wim v2 (wim v0 v3))))))). Qed.

Lemma cd63 (v0 v1 v2 : A)  :
    T (wim (wim (wim v0 v1) v0) (wim (wim v0 v2) v2)).
Proof. exact ((mp (b57 v0 (wim (wim v0 v2) v2) v1) (cd62 v0 v2))). Qed.

Lemma cd64 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))).
Proof. exact ((mp (cd0 (wim v0 v2) v0 (wim (wim v0 v1) v1) v3 (le_l v1 (le_l v1 (below_refl _)))) (cd63 v0 v2 v1))). Qed.

Lemma cd65 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)).
Proof. exact ((mp (b28 (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)) (cd64 v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2))))). Qed.

Lemma cd30 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v3 (wim v2 v0))).
Proof. exact ((mp (b1 (wim v2 v0) v1 v0 v3) (b39 v2 v0 v1))). Qed.

Lemma cd31 (v0 v1 v2 : A)  :
    T (wim v0 (wim v1 (wim v2 v0))).
Proof. exact ((mp (b22 v0 (wim v1 (wim v2 v0)) (wim v2 v0)) (cd30 v0 (wim v1 (wim v2 v0)) v2 v1))). Qed.

Lemma cd66 (v0 v1 v2 v3 : A) (hb0 : v3 ≼ v2) :
    T (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))).
Proof. exact ((mp (cd47 v2 (wim v0 (wim v1 v2)) v3 hb0) (cd31 v2 v0 v1))). Qed.

Lemma cd67 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))).
Proof. exact ((mp (cd66 v0 v1 (wim (wim v0 v2) (wim v3 v2)) v0 (le_l (wim v3 v2) (le_l v2 (below_refl _)))) (cd61 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v2 v3))). Qed.

Lemma cd68 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))).
Proof. exact ((mp (cd65 v0 v1 (wim (wim (wim (wim v0 v1) v1) v2) (wim v3 v2))) (cd67 (wim (wim v0 v1) v1) v0 v2 v3))). Qed.

Lemma cd69 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)).
Proof. exact ((mp (b35 v0 (wim (wim (wim v0 v1) v1) v2) v2) (cd68 v0 v1 v2 v0))). Qed.

Lemma cd76 (v0 v1 v2 : A) (hb0 : v2 ≼ v0) :
    T (wim (wim (wim (wim (wim v0 v1) v1) v2) v0) (wim (wim v0 v1) v1)).
Proof. exact ((mp (cd47 v0 (wim (wim v0 v1) v1) v2 hb0) (cd62 v0 v1))). Qed.

Lemma cd77 (v0 v1 v2 : A)  :
    T (wim (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)).
Proof. exact ((mp (b28 (wim (wim v0 v1) (wim v2 v0)) (wim v2 v0)) (cd30 v0 v1 v2 (wim (wim v0 v1) (wim v2 v0))))). Qed.

Lemma cd80 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)).
Proof. exact ((mp (cd69 v0 v2 (wim (wim (wim v1 (wim (wim v0 v2) v2)) v3) v3)) (cd92 (wim (wim v0 v2) v2) v1 v3))). Qed.

Lemma cd81 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1) v1).
Proof. exact ((mp (cd77 v1 v2 (wim (wim v0 (wim (wim (wim v1 v2) v3) v3)) v1)) (cd80 (wim v1 v2) v0 v3 v1))). Qed.

Lemma cd82 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact ((mp (cd76 v0 (wim (wim (wim v0 v1) v2) v2) v0 (below_refl _)) (cd81 (wim v0 (wim (wim (wim v0 v1) v2) v2)) v0 v1 v2))). Qed.

Lemma cd83 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)).
Proof. exact ((mp (b28 (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v3 v1)) (b20 v0 v1 v2 v3 (wim (wim v0 (wim v1 v2)) (wim v3 v1))))). Qed.

Lemma cd84 (v0 v1 v2 v3 v4 : A)  :
    T (wim (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2) v2).
Proof. exact ((mp (cd83 v1 v2 v3 (wim (wim v0 (wim (wim (wim v1 (wim v2 v3)) v4) v4)) v2)) (cd80 (wim v1 (wim v2 v3)) v0 v4 v2))). Qed.

Lemma cd85 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact ((mp (b46 v0 v1 (wim (wim v2 (wim v0 v3)) v1)) (cd84 (wim v0 v1) v2 v0 v3 v1))). Qed.

Lemma cd86 (v0 v1 v2 : A)  :
    T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact ((mp (cd82 (wim v0 v1) (wim v0 v2) v1) (cd85 v0 v1 (wim v0 v1) v2))). Qed.

Lemma cd87 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact ((mp (cd75 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (cd86 v1 v2 v3))). Qed.

Lemma cd88 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact ((mp (b46 v0 (wim v1 v2) (wim v1 v0)) (cd87 (wim v0 (wim v1 v2)) v1 v0 v2))). Qed.

Lemma cd89 (v0 v1 v2 v3 : A)  :
    T (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact ((mp (cd88 v1 v0 (wim (wim v1 v2) (wim v3 v2))) (cd67 v1 v0 v2 v3))). Qed.

Lemma cd90 (v0 v1 v2 v3 : A)  :
    T (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact ((mp (cd69 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))) (cd89 (wim v0 v1) v1 v2 v3))). Qed.

Lemma cd91 (v0 v1 v2 : A)  :
    T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))).
Proof. exact ((mp (cd35 v0 (wim v0 v1) (wim v1 v2) v2) (cd90 v0 v1 v2 v0))). Qed.

Lemma cd104 (v0 v1 v2 v3 : A)  :
    T (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)).
Proof. exact ((mp (cd91 (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3) (cd91 v2 v0 v1))). Qed.

Lemma cd103 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))).
Proof. exact ((mp (cd104 (wim v1 v2) v2 v0 (wim v1 (wim v0 v2))) (cd69 v1 v2 (wim v0 v2)))). Qed.

Lemma cd105 (v0 v1 v2 : A)  :
    T (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))).
Proof. exact ((mp (cd104 v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2))) (cd88 (wim v1 v2) v0 v2))). Qed.

Lemma cd106 (v0 v1 v2 : A)  :
    T (wim (wim v0 (wim v1 v2)) (wim (wim v0 v1) (wim v0 v2))).
Proof. exact ((mp (cd103 (wim v0 v1) (wim v0 (wim v1 v2)) (wim v0 v2)) (cd105 v0 v1 v2))). Qed.

Lemma basisK (a b : A) : T (wim a (wim b a)).
Proof. exact (b60 a b). Qed.
Lemma basisP (a b : A) : T (wim (wim (wim a b) a) a).
Proof. exact (b25 a b). Qed.
Lemma composition_seed (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (cd91 a b c). Qed.
Lemma distribution_seed (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof. exact (cd106 a b c). Qed.
Lemma compose_derived {a b c : A}
    (hab : T (wim a b)) (hbc : T (wim b c)) : T (wim a c).
Proof. exact (mp (mp (composition_seed a b c) hab) hbc). Qed.
Lemma under_antecedent (z : A) {x y : A}
    (hxy : T (wim x y)) : T (wim (wim z x) (wim z y)).
Proof.
  exact (mp (mp (cd103 (wim z x) (wim x y) (wim z y))
    (composition_seed z x y)) hxy).
Qed.
Lemma rho8_seed (a b c u : A) : T (rho8 a b c u).
Proof.
  exact (compose_derived
    (compose_derived (composition_seed (wim c u) a c)
      (under_antecedent (wim a c) (basisP c u)))
    (under_antecedent (wim a c) (basisK c b))).
Qed.
End Seed.

Theorem rho8_all (a b c u : A) : T (rho8 a b c u).
Proof.
  exact (rho8_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c u).
Qed.
Theorem composition (a b c : A) : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof.
  exact (composition_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c).
Qed.
Theorem distribution (a b c : A) : T (wim (wim a (wim b c)) (wim (wim a b) (wim a c))).
Proof.
  exact (distribution_seed (rho8 a a a a) (row a a a a (below_refl a)) a b c).
Qed.
End Generic.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions distribution.
End DominatedImplication.
