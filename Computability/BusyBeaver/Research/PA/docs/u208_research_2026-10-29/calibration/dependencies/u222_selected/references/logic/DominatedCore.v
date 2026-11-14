(** Copy of rocq224/src/DominatedCore.v (SHA256 e134551b0f0155573293184ad317e3c672476d627d991f661ced653d483992e1) under namespace K217F. *)
(** * DominatedCore: Lukasiewicz's axiom from its dominated instances, and the classical basis.

    For any binary connective [imp] and any reflexive relation [below] preserved by insertion
    into either operand of [imp], modus ponens and the rows [rho8 a b c u] with [below u a]
    derive every row, composition, prefixing, K, Peirce and S. The 56 lemmas are the
    condensed-detachment derivation of k225-formal/rho8cd/derivation_core.txt, rendered by
    generate_domrho8_cd.py --rocq-core exactly as the Lean DominatedImplication. *)

Section Core.
Variable A : Type.
Variable imp : A -> A -> A.
Variable below : A -> A -> Prop.
Hypothesis refl : forall a, below a a.
Hypothesis le_l : forall {u x} y, below u x -> below u (imp x y).
Hypothesis le_r : forall {u y} x, below u y -> below u (imp x y).

Definition rho8 a b c u := imp (imp (imp c u) a) (imp (imp a c) (imp b c)).

Variable T : A -> Prop.
Hypothesis mp : forall a b, T (imp a b) -> T a -> T b.
Hypothesis row : forall a b c u, below u a -> T (rho8 a b c u).

Lemma d1 v0 v1 v2 v3 v4 (hb0 : below v3 v0) :
  T (imp (imp (imp (imp v0 v1) (imp v2 v1)) (imp v1 v3)) (imp v4 (imp v1 v3))).
Proof. exact (mp _ _ (row (imp (imp v0 v1) (imp v2 v1)) v4 (imp v1 v3) v0 (le_l (imp v2 v1) (le_l v1 (refl _)))) (row v0 v2 v1 v3 hb0)). Qed.

Lemma d2 v0 v1 v2 v3 v4 v5 (hb0 : below v2 v3) :
  T (imp (imp (imp v0 (imp v1 v2)) (imp (imp v3 v1) (imp v4 v1))) (imp v5 (imp (imp v3 v1) (imp v4 v1)))).
Proof. exact (mp _ _ (row (imp v0 (imp v1 v2)) v5 (imp (imp v3 v1) (imp v4 v1)) (imp v1 v2) (le_r v0 (refl _))) (d1 v3 v1 v4 v2 v0 hb0)). Qed.

Lemma d3 v0 v1 v2 v3 :
  T (imp v0 (imp (imp (imp v1 v2) v1) (imp v3 v1))).
Proof. exact (mp _ _ (d2 (imp v1 (imp v1 v2)) v1 v2 (imp v1 v2) v3 v0 (le_r v1 (refl _))) (row (imp v1 v2) v3 v1 (imp v1 v2) (refl _))). Qed.

Lemma d4 v0 v1 v2 :
  T (imp (imp (imp v0 v1) v0) (imp v2 v0)).
Proof. exact (mp _ _ (d3 (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _))). Qed.

Lemma d5 v0 v1 v2 v3 :
  T (imp (imp (imp v0 v1) (imp v1 v2)) (imp v3 (imp v1 v2))).
Proof. exact (mp _ _ (row (imp v0 v1) v3 (imp v1 v2) v1 (le_r v0 (refl _))) (d4 v1 v2 v0)). Qed.

Lemma d6 v0 v1 v2 v3 v4 :
  T (imp (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v4 (imp v3 v1))).
Proof. exact (mp _ _ (row (imp v0 (imp v1 v2)) v4 (imp v3 v1) (imp v1 v2) (le_r v0 (refl _))) (d5 v3 v1 v2 v0)). Qed.

Lemma d7 v0 v1 v2 v3 :
  T (imp v0 (imp (imp (imp (imp v1 v2) v3) v2) (imp v1 v2))).
Proof. exact (mp _ _ (d6 (imp v2 (imp (imp v1 v2) v3)) (imp v1 v2) v3 (imp (imp (imp v1 v2) v3) v2) v0) (row (imp (imp v1 v2) v3) v1 v2 (imp (imp v1 v2) v3) (refl _))). Qed.

Lemma d8 v0 v1 v2 v3 v4 v5 :
  T (imp (imp (imp v0 (imp v1 v2)) (imp v3 (imp v2 v4))) (imp v5 (imp v3 (imp v2 v4)))).
Proof. exact (mp _ _ (row (imp v0 (imp v1 v2)) v5 (imp v3 (imp v2 v4)) (imp v1 v2) (le_r v0 (refl _))) (d6 v3 v2 v4 v1 v0)). Qed.

Lemma d9 v0 v1 v2 :
  T (imp (imp (imp (imp v0 v1) v2) v1) (imp v0 v1)).
Proof. exact (mp _ _ (d7 (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _))). Qed.

Lemma d10 v0 v1 v2 v3 :
  T (imp v0 (imp (imp (imp v1 v2) v3) (imp v2 v3))).
Proof. exact (mp _ _ (d8 (imp v3 (imp v1 v2)) v1 v2 (imp (imp v1 v2) v3) v3 v0) (row (imp v1 v2) v2 v3 (imp v1 v2) (refl _))). Qed.

Lemma d11 v0 v1 v2 v3 :
  T (imp (imp (imp v0 v1) (imp (imp v0 v1) v2)) (imp v3 (imp (imp v0 v1) v2))).
Proof. exact (mp _ _ (row (imp v0 v1) v3 (imp (imp v0 v1) v2) v1 (le_r v0 (refl _))) (d9 v0 v1 v2)). Qed.

Lemma d12 v0 v1 :
  T (imp v0 (imp v1 v0)).
Proof. exact (mp _ _ (d9 v0 (imp v1 v0) v0) (d4 v0 (imp v1 v0) v1)). Qed.

Lemma d13 v0 v1 v2 :
  T (imp (imp (imp v0 v1) v2) (imp v1 v2)).
Proof. exact (mp _ _ (d10 (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2) (row v0 v0 v0 v0 (refl _))). Qed.

Lemma d14 v0 v1 v2 :
  T (imp v0 (imp (imp (imp v1 v2) v1) v1)).
Proof. exact (mp _ _ (d11 (imp v1 v2) v1 v1 v0) (d4 v1 v2 (imp (imp v1 v2) v1))). Qed.

Lemma d15 v0 v1 v2 v3 :
  T (imp (imp (imp v0 (imp v1 v2)) v1) (imp v3 v1)).
Proof. exact (mp _ _ (row (imp v0 (imp v1 v2)) v3 v1 v2 (le_r v0 (le_r v1 (refl _)))) (d12 (imp v1 v2) v0)). Qed.

Lemma d16 v0 v1 v2 :
  T (imp v0 (imp (imp v0 v1) (imp v2 v1))).
Proof. exact (mp _ _ (d13 (imp v1 v0) v0 (imp (imp v0 v1) (imp v2 v1))) (row v0 v2 v1 v0 (refl _))). Qed.

Lemma d17 v0 v1 v2 :
  T (imp v0 (imp v1 (imp v2 v0))).
Proof. exact (mp _ _ (d13 v2 v0 (imp v1 (imp v2 v0))) (d12 (imp v2 v0) v1)). Qed.

Lemma d18 v0 v1 :
  T (imp (imp (imp v0 v1) v0) v0).
Proof. exact (mp _ _ (d14 (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _))). Qed.

Lemma d19 v0 v1 v2 v3 v4 :
  T (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) (imp v4 v0)).
Proof. exact (mp _ _ (row (imp (imp (imp v0 v1) v2) (imp v3 v2)) v4 v0 v1 (le_l (imp v3 v2) (le_l v2 (le_r v0 (refl _))))) (d16 (imp v0 v1) v2 v3)). Qed.

Lemma d20 v0 v1 v2 :
  T (imp (imp v0 (imp v0 v1)) (imp v2 (imp v0 v1))).
Proof. exact (mp _ _ (row v0 v2 (imp v0 v1) v0 (refl _)) (d18 v0 v1)). Qed.

Lemma d21 v0 v1 v2 :
  T (imp v0 (imp (imp v1 (imp v1 v2)) (imp v1 v2))).
Proof. exact (mp _ _ (d11 v1 (imp v1 v2) (imp v1 v2) v0) (d20 v1 v2 (imp v1 (imp v1 v2)))). Qed.

Lemma d22 v0 v1 :
  T (imp (imp v0 (imp v0 v1)) (imp v0 v1)).
Proof. exact (mp _ _ (d21 (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1) (row v0 v0 v0 v0 (refl _))). Qed.

Lemma d23 v0 v1 v2 :
  T (imp (imp (imp v0 (imp v1 v2)) v1) v1).
Proof. exact (mp _ _ (d22 (imp (imp v0 (imp v1 v2)) v1) v1) (d15 v0 v1 v2 (imp (imp v0 (imp v1 v2)) v1))). Qed.

Lemma d24 v0 v1 v2 v3 :
  T (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0).
Proof. exact (mp _ _ (d22 (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0) (d19 v0 v1 v2 v3 (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0))). Qed.

Lemma d25 v0 v1 v2 v3 :
  T (imp (imp v0 (imp v1 (imp v0 v2))) (imp v3 (imp v1 (imp v0 v2)))).
Proof. exact (mp _ _ (row v0 v3 (imp v1 (imp v0 v2)) v0 (refl _)) (d23 v1 v0 v2)). Qed.

Lemma d26 v0 v1 v2 v3 v4 :
  T (imp (imp v0 (imp (imp (imp v0 v1) v2) (imp v3 v2))) (imp v4 (imp (imp (imp v0 v1) v2) (imp v3 v2)))).
Proof. exact (mp _ _ (row v0 v4 (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0 (refl _)) (d24 v0 v1 v2 v3)). Qed.

Lemma d27 v0 v1 v2 :
  T (imp (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))).
Proof. exact (mp _ _ (d22 (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))) (d25 v0 v1 v2 (imp v0 (imp v1 (imp v0 v2))))). Qed.

Lemma d28 v0 v1 v2 v3 v4 v5 :
  T (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) (imp v4 v3))) v1) (imp v5 v1)).
Proof. exact (mp _ _ (row (imp v0 (imp (imp (imp v1 v2) v3) (imp v4 v3))) v5 v1 (imp (imp (imp v1 v2) v3) (imp v4 v3)) (le_r v0 (refl _))) (d26 v1 v2 v3 v4 v0)). Qed.

Lemma d29 v0 v1 v2 v3 v4 :
  T (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) (imp v4 v3))) v1) v1).
Proof. exact (mp _ _ (d22 (imp (imp v0 (imp (imp (imp v1 v2) v3) (imp v4 v3))) v1) v1) (d28 v0 v1 v2 v3 v4 (imp (imp v0 (imp (imp (imp v1 v2) v3) (imp v4 v3))) v1))). Qed.

Lemma d30 v0 v1 v2 (hb0 : below v2 v0) :
  T (imp (imp v0 v1) (imp (imp (imp v1 v2) v0) v1)).
Proof. exact (mp _ _ (d27 (imp (imp v1 v2) v0) (imp v0 v1) v1) (row v0 (imp (imp v1 v2) v0) v1 v2 hb0)). Qed.

Lemma d31 v0 v1 v2 v3 (hb0 : below v3 v0) :
  T (imp (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) v0) (imp (imp v0 v1) (imp v2 v1))).
Proof. exact (mp _ _ (d30 v0 (imp (imp v0 v1) (imp v2 v1)) v3 hb0) (d16 v0 v1 v2)). Qed.

Lemma d32 v0 v1 v2 v3 :
  T (imp (imp v0 (imp v1 v2)) (imp (imp (imp v0 v3) v2) (imp v1 v2))).
Proof. exact (mp _ _ (d31 v0 (imp v1 v2) (imp (imp v0 v3) v2) v0 (refl _)) (d29 (imp v0 (imp v1 v2)) v0 v3 v2 v1)). Qed.

Lemma d33 v0 v1 v2 v3 :
  T (imp (imp (imp v0 v1) (imp v2 v3)) (imp (imp v0 v3) (imp v2 v3))).
Proof. exact (mp _ _ (d32 v0 (imp v0 v3) (imp v2 v3) v1) (d16 v0 v3 v2)). Qed.

Lemma d34 v0 v1 v2 v3 (hb0 : below v3 v2) :
  T (imp (imp (imp (imp v0 (imp v1 v2)) v3) v2) (imp v0 (imp v1 v2))).
Proof. exact (mp _ _ (d30 v2 (imp v0 (imp v1 v2)) v3 hb0) (d17 v2 v0 v1)). Qed.

Lemma d35 v0 v1 v2 v3 :
  T (imp v0 (imp v1 (imp (imp v0 v2) (imp v3 v2)))).
Proof. exact (mp _ _ (d34 v0 v1 (imp (imp v0 v2) (imp v3 v2)) (imp v3 v2) (le_r (imp v0 v2) (refl _))) (d33 v0 (imp v1 (imp (imp v0 v2) (imp v3 v2))) v3 v2)). Qed.

Lemma d36 v0 v1 v2 v3 (hb0 : below v3 (imp v1 (imp v1 v2))) :
  T (imp (imp (imp (imp v0 (imp v1 v2)) v3) (imp v1 (imp v1 v2))) (imp v0 (imp v1 v2))).
Proof. exact (mp _ _ (d30 (imp v1 (imp v1 v2)) (imp v0 (imp v1 v2)) v3 hb0) (d20 v1 v2 v0)). Qed.

Lemma d37 v0 v1 :
  T (imp v0 (imp (imp v0 v1) v1)).
Proof. exact (mp _ _ (d36 v0 (imp v0 v1) v1 (imp (imp v0 v1) v1) (le_r (imp v0 v1) (refl _))) (d33 v0 (imp (imp v0 v1) v1) (imp v0 v1) v1)). Qed.

Lemma d38 v0 v1 v2 :
  T (imp v0 (imp (imp (imp v1 v0) v2) v2)).
Proof. exact (mp _ _ (d13 v1 v0 (imp (imp (imp v1 v0) v2) v2)) (d37 (imp v1 v0) v2)). Qed.

Lemma d39 v0 v1 v2 :
  T (imp (imp (imp v0 v1) v2) (imp (imp v0 v2) v2)).
Proof. exact (mp _ _ (d32 v0 (imp v0 v2) v2 v1) (d37 v0 v2)). Qed.

Lemma d40 v0 v1 v2 v3 :
  T (imp (imp (imp v0 v1) v2) (imp (imp (imp v3 v0) v2) v2)).
Proof. exact (mp _ _ (d32 v0 (imp (imp v3 v0) v2) v2 v1) (d38 v0 v3 v2)). Qed.

Lemma d41 v0 v1 v2 v3 :
  T (imp (imp v0 v1) (imp (imp (imp v2 (imp v0 v3)) v1) v1)).
Proof. exact (mp _ _ (d33 v0 v3 (imp (imp v2 (imp v0 v3)) v1) v1) (d38 (imp v0 v3) v2 v1)). Qed.

Lemma d42 v0 v1 v2 v3 :
  T (imp (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v1 (imp v2 (imp v0 v3)))).
Proof. exact (mp _ _ (d39 v0 v3 (imp v1 (imp v2 (imp v0 v3)))) (d17 (imp v0 v3) v1 v2)). Qed.

Lemma d43 v0 v1 v2 :
  T (imp (imp v0 (imp (imp (imp v0 v1) v2) v2)) (imp (imp (imp v0 v1) v2) v2)).
Proof. exact (mp _ _ (d39 v0 v1 (imp (imp (imp v0 v1) v2) v2)) (d37 (imp v0 v1) v2)). Qed.

Lemma d44 v0 v1 v2 :
  T (imp (imp (imp (imp v0 v1) (imp v0 v2)) v1) v1).
Proof. exact (mp _ _ (d43 (imp v0 v1) (imp v0 v2) v1) (d41 v0 v1 (imp v0 v1) v2)). Qed.

Lemma d45 v0 v1 v2 v3 :
  T (imp (imp (imp v0 (imp (imp v1 v2) (imp v1 v3))) v2) v2).
Proof. exact (mp _ _ (d40 (imp (imp v1 v2) (imp v1 v3)) v2 v2 v0) (d44 v1 v2 v3)). Qed.

Lemma d46 v0 v1 v2 :
  T (imp (imp v0 (imp v1 v2)) (imp (imp v1 v0) (imp v1 v2))).
Proof. exact (mp _ _ (d31 v0 (imp v1 v2) (imp v1 v0) v0 (refl _)) (d45 (imp v0 (imp v1 v2)) v1 v0 v2)). Qed.

Lemma d47 v0 v1 v2 v3 :
  T (imp (imp v0 v1) (imp v0 (imp (imp v1 v2) (imp v3 v2)))).
Proof. exact (mp _ _ (d46 v1 v0 (imp (imp v1 v2) (imp v3 v2))) (d35 v1 v0 v2 v3)). Qed.

Lemma d48 v0 v1 v2 v3 :
  T (imp v0 (imp (imp (imp (imp v0 v1) v1) v2) (imp v3 v2))).
Proof. exact (mp _ _ (d47 v0 (imp (imp v0 v1) v1) v2 v3) (d37 v0 v1)). Qed.

Lemma d49 v0 v1 v2 :
  T (imp (imp (imp (imp v0 v1) v1) v2) (imp v0 v2)).
Proof. exact (mp _ _ (d27 v0 (imp (imp (imp v0 v1) v1) v2) v2) (d48 v0 v1 v2 v0)). Qed.

Lemma d50 v0 v1 v2 v3 :
  T (imp v0 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))).
Proof. exact (mp _ _ (d49 v0 v1 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))) (d47 (imp v0 v1) v1 v2 v3)). Qed.

Lemma d51 v0 v1 v2 :
  T (imp (imp v0 v1) (imp (imp v1 v2) (imp v0 v2))).
Proof. exact (mp _ _ (d42 v0 (imp v0 v1) (imp v1 v2) v2) (d50 v0 v1 v2 v0)). Qed.

Lemma d52 v0 v1 v2 v3 :
  T (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) (imp (imp v2 v0) v3)).
Proof. exact (mp _ _ (d51 (imp v2 v0) (imp (imp v0 v1) (imp v2 v1)) v3) (d51 v2 v0 v1)). Qed.

Lemma d53 v0 v1 v2 :
  T (imp (imp v0 v1) (imp (imp v0 (imp v1 v2)) (imp v0 v2))).
Proof. exact (mp _ _ (d52 v1 v2 v0 (imp (imp v0 (imp v1 v2)) (imp v0 v2))) (d46 (imp v1 v2) v0 v2)). Qed.

Lemma d54 v0 v1 v2 :
  T (imp (imp v0 (imp v1 v2)) (imp v1 (imp v0 v2))).
Proof. exact (mp _ _ (d52 (imp v1 v2) v2 v0 (imp v1 (imp v0 v2))) (d49 v1 v2 (imp v0 v2))). Qed.

Lemma d55 v0 v1 v2 :
  T (imp (imp v0 v1) (imp (imp v2 v0) (imp v2 v1))).
Proof. exact (mp _ _ (d49 (imp v0 v1) (imp v2 v1) (imp (imp v2 v0) (imp v2 v1))) (d52 v0 v1 v2 (imp v2 v1))). Qed.

Lemma d57 v0 v1 v2 v3 :
  T (imp (imp v0 (imp (imp v1 v2) v1)) (imp v0 (imp v3 v1))).
Proof. exact (mp _ _ (d55 (imp (imp v1 v2) v1) (imp v3 v1) v0) (d4 v1 v2 v3)). Qed.

(** Restricted rows and modus ponens alone derive every unrestricted row. *)
Theorem rho8_all a b c u : T (rho8 a b c u).
Proof. exact (mp _ _ (d52 a c (imp c u) (imp (imp a c) (imp b c))) (d57 (imp a c) c u b)). Qed.

Theorem composition a b c : T (imp (imp a b) (imp (imp b c) (imp a c))).
Proof. exact (d51 a b c). Qed.

(** A proved implication lifts under any antecedent. *)
Theorem lift_right a b (hab : T (imp a b)) x : T (imp (imp x a) (imp x b)).
Proof. exact (mp _ _ (d55 a b x) hab). Qed.

Theorem k a b : T (imp a (imp b a)).
Proof. exact (d12 a b). Qed.

Theorem peirce a b : T (imp (imp (imp a b) a) a).
Proof. exact (d18 a b). Qed.

Theorem s a b c : T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))).
Proof. exact (mp _ _ (d54 (imp a b) (imp a (imp b c)) (imp a c)) (d53 a b c)). Qed.

End Core.
Print Assumptions s.
