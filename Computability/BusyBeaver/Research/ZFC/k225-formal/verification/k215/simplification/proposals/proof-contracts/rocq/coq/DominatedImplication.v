(** Representation-independent dominated implication, without a truth premise.
    Generated from the SAME 58-step derivation_core.txt used by the maintained
    Lean core. Only modus ponens, the restricted row, and subterm growth are used.
    No formula decoder, arithmetic coding, injectivity, transitivity, or truth
    constant is assumed. The generator is untrusted; every lemma is checked. *)
Set Universe Polymorphism.
Module DominatedImplication.
Section Derivation.
Context {A : Type}.
Variable wim : A -> A -> A.
Variable below : A -> A -> Prop.
Hypothesis below_refl : forall a, below a a.
Hypothesis grow_left : forall u x y, below u x -> below u (wim x y).
Hypothesis grow_right : forall u x y, below u y -> below u (wim x y).

Definition rho8 (a b c u : A) : A :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c)).

Variable T : A -> Prop.
Hypothesis dmp : forall a b, T (wim a b) -> T a -> T b.
Hypothesis drho8 : forall a b c u, below u a -> T (rho8 a b c u).

Local Definition le_l {u x : A} y (H : below u x) : below u (wim x y) :=
  grow_left u x y H.
Local Definition le_r {u y : A} x (H : below u y) : below u (wim x y) :=
  grow_right u x y H.

Lemma d1 (v0 v1 v2 v3 v4 : A) (hb0 : below v3 v0) :
  T (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))).
Proof. exact (dmp _ _ (drho8 (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0 (le_l (wim v2 v1) (le_l v1 (below_refl _)))) (drho8 v0 v2 v1 v3 hb0)). Qed.

Lemma d2 (v0 v1 v2 v3 v4 v5 : A) (hb0 : below v2 v3) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))).
Proof. exact (dmp _ _ (drho8 (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2) (le_r v0 (below_refl _))) (d1 v3 v1 v4 v2 v0 hb0)). Qed.

Lemma d3 (v0 v1 v2 v3 : A) :
  T (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))).
Proof. exact (dmp _ _ (d2 (wim v1 (wim v1 v2)) v1 v2 (wim v1 v2) v3 v0 (le_r v1 (below_refl _))) (drho8 (wim v1 v2) v3 v1 (wim v1 v2) (below_refl _))). Qed.

Lemma d4 (v0 v1 v2 : A) :
  T (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact (dmp _ _ (d3 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (drho8 v0 v0 v0 v0 (below_refl _))). Qed.

Lemma d5 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact (dmp _ _ (drho8 (wim v0 v1) v3 (wim v1 v2) v1 (le_r v0 (below_refl _))) (d4 v1 v2 v0)). Qed.

Lemma d6 (v0 v1 v2 v3 v4 : A) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact (dmp _ _ (drho8 (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2) (le_r v0 (below_refl _))) (d5 v3 v1 v2 v0)). Qed.

Lemma d7 (v0 v1 v2 v3 : A) :
  T (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact (dmp _ _ (d6 (wim v2 (wim (wim v1 v2) v3)) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0) (drho8 (wim (wim v1 v2) v3) v1 v2 (wim (wim v1 v2) v3) (below_refl _))). Qed.

Lemma d8 (v0 v1 v2 v3 v4 v5 : A) :
  T (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact (dmp _ _ (drho8 (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2) (le_r v0 (below_refl _))) (d6 v3 v2 v4 v1 v0)). Qed.

Lemma d9 (v0 v1 v2 : A) :
  T (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact (dmp _ _ (d7 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (drho8 v0 v0 v0 v0 (below_refl _))). Qed.

Lemma d10 (v0 v1 v2 v3 : A) :
  T (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact (dmp _ _ (d8 (wim v3 (wim v1 v2)) v1 v2 (wim (wim v1 v2) v3) v3 v0) (drho8 (wim v1 v2) v2 v3 (wim v1 v2) (below_refl _))). Qed.

Lemma d11 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact (dmp _ _ (drho8 (wim v0 v1) v3 (wim (wim v0 v1) v2) v1 (le_r v0 (below_refl _))) (d9 v0 v1 v2)). Qed.

Lemma d12 (v0 v1 : A) :
  T (wim v0 (wim v1 v0)).
Proof. exact (dmp _ _ (d9 v0 (wim v1 v0) v0) (d4 v0 (wim v1 v0) v1)). Qed.

Lemma d13 (v0 v1 v2 : A) :
  T (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact (dmp _ _ (d10 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2) (drho8 v0 v0 v0 v0 (below_refl _))). Qed.

Lemma d14 (v0 v1 v2 : A) :
  T (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact (dmp _ _ (d11 (wim v1 v2) v1 v1 v0) (d4 v1 v2 (wim (wim v1 v2) v1))). Qed.

Lemma d15 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact (dmp _ _ (drho8 (wim v0 (wim v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (below_refl _)))) (d12 (wim v1 v2) v0)). Qed.

Lemma d16 (v0 v1 v2 : A) :
  T (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (dmp _ _ (d13 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1))) (drho8 v0 v2 v1 v0 (below_refl _))). Qed.

Lemma d17 (v0 v1 v2 : A) :
  T (wim v0 (wim v1 (wim v2 v0))).
Proof. exact (dmp _ _ (d13 v2 v0 (wim v1 (wim v2 v0))) (d12 (wim v2 v0) v1)). Qed.

Lemma d18 (v0 v1 : A) :
  T (wim (wim (wim v0 v1) v0) v0).
Proof. exact (dmp _ _ (d14 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (drho8 v0 v0 v0 v0 (below_refl _))). Qed.

Lemma d19 (v0 v1 v2 v3 v4 : A) :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact (dmp _ _ (drho8 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1 (le_l (wim v3 v2) (le_l v2 (le_r v0 (below_refl _))))) (d16 (wim v0 v1) v2 v3)). Qed.

Lemma d20 (v0 v1 v2 : A) :
  T (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact (dmp _ _ (drho8 v0 v2 (wim v0 v1) v0 (below_refl _)) (d18 v0 v1)). Qed.

Lemma d21 (v0 v1 v2 : A) :
  T (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact (dmp _ _ (d11 v1 (wim v1 v2) (wim v1 v2) v0) (d20 v1 v2 (wim v1 (wim v1 v2)))). Qed.

Lemma d22 (v0 v1 : A) :
  T (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact (dmp _ _ (d21 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1) (drho8 v0 v0 v0 v0 (below_refl _))). Qed.

Lemma d23 (v0 v1 v2 : A) :
  T (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact (dmp _ _ (d22 (wim (wim v0 (wim v1 v2)) v1) v1) (d15 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1))). Qed.

Lemma d24 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact (dmp _ _ (d22 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0) (d19 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0))). Qed.

Lemma d25 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact (dmp _ _ (drho8 v0 v3 (wim v1 (wim v0 v2)) v0 (below_refl _)) (d23 v1 v0 v2)). Qed.

Lemma d26 (v0 v1 v2 v3 v4 : A) :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact (dmp _ _ (drho8 v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0 (below_refl _)) (d24 v0 v1 v2 v3)). Qed.

Lemma d27 (v0 v1 v2 : A) :
  T (wim (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))).
Proof. exact (dmp _ _ (d22 (wim v0 (wim v1 (wim v0 v2))) (wim v1 (wim v0 v2))) (d25 v0 v1 v2 (wim v0 (wim v1 (wim v0 v2))))). Qed.

Lemma d28 (v0 v1 v2 v3 v4 v5 : A) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact (dmp _ _ (drho8 (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)) (le_r v0 (below_refl _))) (d26 v1 v2 v3 v4 v0)). Qed.

Lemma d29 (v0 v1 v2 v3 v4 : A) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact (dmp _ _ (d22 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1) (d28 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1))). Qed.

Lemma d30 (v0 v1 v2 : A) (hb0 : below v2 v0) :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (dmp _ _ (d27 (wim (wim v1 v2) v0) (wim v0 v1) v1) (drho8 v0 (wim (wim v1 v2) v0) v1 v2 hb0)). Qed.

Lemma d31 (v0 v1 v2 v3 : A) (hb0 : below v3 v0) :
  T (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (dmp _ _ (d30 v0 (wim (wim v0 v1) (wim v2 v1)) v3 hb0) (d16 v0 v1 v2)). Qed.

Lemma d32 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 (wim (wim v1 v2) v3)) v2) (wim v1 v2)).
Proof. exact (dmp _ _ (d31 (wim v0 (wim (wim v1 v2) v3)) v2 v1 (wim (wim v1 v2) v3) (le_r v0 (below_refl _))) (d5 (wim (wim v0 (wim (wim v1 v2) v3)) v2) (wim v1 v2) v3 v0)). Qed.

Lemma d33 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact (dmp _ _ (d31 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0 (below_refl _)) (d29 (wim v0 (wim v1 v2)) v0 v3 v2 v1)). Qed.

Lemma d34 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))).
Proof. exact (dmp _ _ (d33 v0 (wim v0 v3) (wim v2 v3) v1) (d16 v0 v3 v2)). Qed.

Lemma d35 (v0 v1 v2 v3 : A) (hb0 : below v3 (wim v1 (wim v1 v2))) :
  T (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact (dmp _ _ (d30 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3 hb0) (d20 v1 v2 v0)). Qed.

Lemma d36 (v0 v1 : A) :
  T (wim v0 (wim (wim v0 v1) v1)).
Proof. exact (dmp _ _ (d35 v0 (wim v0 v1) v1 (wim (wim v0 v1) v1) (le_r (wim v0 v1) (below_refl _))) (d34 v0 (wim (wim v0 v1) v1) (wim v0 v1) v1)). Qed.

Lemma d37 (v0 v1 v2 : A) :
  T (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact (dmp _ _ (d13 v1 v0 (wim (wim (wim v1 v0) v2) v2)) (d36 (wim v1 v0) v2)). Qed.

Lemma d38 (v0 v1 v2 : A) :
  T (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)).
Proof. exact (dmp _ _ (d33 v0 (wim v0 v2) v2 v1) (d36 v0 v2)). Qed.

Lemma d39 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact (dmp _ _ (d33 v0 (wim (wim v3 v0) v2) v2 v1) (d37 v0 v3 v2)). Qed.

Lemma d40 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact (dmp _ _ (d34 v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1) (d37 (wim v0 v3) v2 v1)). Qed.

Lemma d41 (v0 v1 v2 : A) :
  T (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact (dmp _ _ (d38 v0 v1 (wim (wim (wim v0 v1) v2) v2)) (d36 (wim v0 v1) v2)). Qed.

Lemma d42 (v0 v1 v2 : A) :
  T (wim (wim (wim (wim (wim v0 v1) v2) v0) v2) v2).
Proof. exact (dmp _ _ (d41 (wim (wim v0 v1) v2) v0 v2) (d39 v0 v1 v2 (wim (wim v0 v1) v2))). Qed.

Lemma d43 (v0 v1 v2 : A) :
  T (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact (dmp _ _ (d41 (wim v0 v1) (wim v0 v2) v1) (d40 v0 v1 (wim v0 v1) v2)). Qed.

Lemma d44 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) v1)) v3) v3).
Proof. exact (dmp _ _ (d39 (wim (wim (wim v1 v2) v3) v1) v3 v3 v0) (d42 v1 v2 v3)). Qed.

Lemma d45 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact (dmp _ _ (d39 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0) (d43 v1 v2 v3)). Qed.

Lemma d46 (v0 v1 v2 : A) :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (dmp _ _ (d31 v0 v1 (wim (wim v1 v2) v0) v0 (below_refl _)) (d44 (wim v0 v1) v1 v2 v0)). Qed.

Lemma d47 (v0 v1 v2 : A) :
  T (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact (dmp _ _ (d31 v0 (wim v1 v2) (wim v1 v0) v0 (below_refl _)) (d45 (wim v0 (wim v1 v2)) v1 v0 v2)). Qed.

Lemma d48 (v0 v1 v2 : A) :
  T (wim (wim v0 v1) (wim v0 (wim v2 v1))).
Proof. exact (dmp _ _ (d47 v1 v0 (wim v2 v1)) (d17 v1 v0 v2)). Qed.

Lemma d49 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 v1) (wim v2 (wim v0 (wim v3 v1)))).
Proof. exact (dmp _ _ (d48 (wim v0 v1) (wim v0 (wim v3 v1)) v2) (d48 v0 v1 v3)). Qed.

Lemma d50 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 (wim v1 v2)) (wim v0 (wim v1 (wim v3 v2)))).
Proof. exact (dmp _ _ (d47 (wim v1 v2) v0 (wim v1 (wim v3 v2))) (d49 v1 v2 v0 v3)). Qed.

Lemma d51 (v0 v1 v2 v3 v4 : A) :
  T (wim (wim (wim v0 (wim (wim v1 v2) v3)) v2) (wim v1 (wim v4 v2))).
Proof. exact (dmp _ _ (d50 (wim (wim v0 (wim (wim v1 v2) v3)) v2) v1 v2 v4) (d32 v0 v1 v2 v3)). Qed.

Lemma d52 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) (wim v3 v1))).
Proof. exact (dmp _ _ (d50 (wim v0 v1) (wim (wim v1 v2) v0) v1 v3) (d46 v0 v1 v2)). Qed.

Lemma d53 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 (wim v1 v2)) v3) (wim (wim v0 v2) v3)).
Proof. exact (dmp _ _ (d31 (wim v0 (wim v1 v2)) v3 (wim v0 v2) v2 (le_r v0 (le_r v1 (below_refl _)))) (d51 (wim (wim v0 (wim v1 v2)) v3) v0 v2 v3 v1)). Qed.

Lemma d54 (v0 v1 v2 : A) :
  T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) v0)).
Proof. exact (dmp _ _ (d27 (wim v2 v0) (wim (wim v0 v1) v2) v0) (d52 v2 v0 v1 (wim v2 v0))). Qed.

Lemma d55 (v0 v1 v2 : A) :
  T (wim (wim v0 v1) (wim (wim v2 v0) (wim v2 v1))).
Proof. exact (dmp _ _ (d53 v0 v2 v1 (wim (wim v2 v0) (wim v2 v1))) (d47 v0 v2 v1)). Qed.

Lemma d56 (v0 v1 v2 v3 : A) :
  T (wim (wim (wim v0 v1) v2) (wim (wim v2 v0) (wim v3 v0))).
Proof. exact (dmp _ _ (d50 (wim (wim v0 v1) v2) (wim v2 v0) v0 v3) (d54 v0 v1 v2)). Qed.

Lemma d57 (v0 v1 v2 v3 : A) :
  T (wim (wim v0 v1) (wim (wim v2 v0) (wim v3 (wim v2 v1)))).
Proof. exact (dmp _ _ (d50 (wim v0 v1) (wim v2 v0) (wim v2 v1) v3) (d55 v0 v1 v2)). Qed.

Lemma d58 (v0 v1 v2 : A) :
  T (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))).
Proof. exact (dmp _ _ (d27 (wim v1 v2) (wim v0 v1) (wim v0 v2)) (d57 v1 v2 v0 (wim v1 v2))). Qed.

Theorem rho8_all (a b c u : A) : T (rho8 a b c u).
Proof. exact (d56 c u a b). Qed.

Theorem composition (a b c : A) :
  T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (d58 a b c). Qed.

Theorem lift_right (a b : A) (hab : T (wim a b)) (x : A) :
  T (wim (wim x a) (wim x b)).
Proof. exact (dmp _ _ (d55 a b x) hab). Qed.

End Derivation.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions lift_right.
End DominatedImplication.
