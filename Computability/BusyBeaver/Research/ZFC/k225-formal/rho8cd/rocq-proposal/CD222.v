(** * CD222: implicational theorems of thm222 from the Lukasiewicz row rho8 alone.

    The 56 lemmas are the condensed-detachment derivation of k225-formal/rho8cd/derivation_luk.txt,
    rendered by generate_domrho8_cd.py --rocq-cd exactly as the Lean Lukasiewicz.lean (the search
    that found it, seeded with the statements of the pinned m254/CD254.v, is untrusted). *)
From K230L Require Import Codes230.
From K215F Require Import Thm222.

Lemma d1 (v0 v1 v2 v3 v4 : nat) : thm222 (wim (wim (wim (wim v0 v1) (wim v2 v1)) (wim v1 v3)) (wim v4 (wim v1 v3))).
Proof. exact (W_mp _ _ (W_r8 v0 v2 v1 v3) (W_r8 (wim (wim v0 v1) (wim v2 v1)) v4 (wim v1 v3) v0)). Qed.
Lemma d2 (v0 v1 v2 v3 v4 v5 : nat) : thm222 (wim (wim (wim v0 (wim v1 v2)) (wim (wim v3 v1) (wim v4 v1))) (wim v5 (wim (wim v3 v1) (wim v4 v1)))).
Proof. exact (W_mp _ _ (d1 v3 v1 v4 v2 v0) (W_r8 (wim v0 (wim v1 v2)) v5 (wim (wim v3 v1) (wim v4 v1)) (wim v1 v2))). Qed.
Lemma d3 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim (wim (wim v1 v2) v1) (wim v3 v1))).
Proof. exact (W_mp _ _ (W_r8 (wim v1 v2) v3 v1 v0) (d2 (wim v1 v0) v1 v2 (wim v1 v2) v3 v0)). Qed.
Lemma d4 (v0 v1 v2 : nat) : thm222 (wim (wim (wim v0 v1) v0) (wim v2 v0)).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d3 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2)). Qed.
Lemma d5 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 v1) (wim v1 v2)) (wim v3 (wim v1 v2))).
Proof. exact (W_mp _ _ (d4 v1 v2 v0) (W_r8 (wim v0 v1) v3 (wim v1 v2) v1)). Qed.
Lemma d6 (v0 v1 v2 v3 v4 : nat) : thm222 (wim (wim (wim v0 (wim v1 v2)) (wim v3 v1)) (wim v4 (wim v3 v1))).
Proof. exact (W_mp _ _ (d5 v3 v1 v2 v0) (W_r8 (wim v0 (wim v1 v2)) v4 (wim v3 v1) (wim v1 v2))). Qed.
Lemma d7 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim (wim (wim (wim v1 v2) v3) v2) (wim v1 v2))).
Proof. exact (W_mp _ _ (W_r8 (wim (wim v1 v2) v3) v1 v2 v0) (d6 (wim v2 v0) (wim v1 v2) v3 (wim (wim (wim v1 v2) v3) v2) v0)). Qed.
Lemma d8 (v0 v1 v2 v3 v4 v5 : nat) : thm222 (wim (wim (wim v0 (wim v1 v2)) (wim v3 (wim v2 v4))) (wim v5 (wim v3 (wim v2 v4)))).
Proof. exact (W_mp _ _ (d6 v3 v2 v4 v1 v0) (W_r8 (wim v0 (wim v1 v2)) v5 (wim v3 (wim v2 v4)) (wim v1 v2))). Qed.
Lemma d9 (v0 v1 v2 : nat) : thm222 (wim (wim (wim (wim v0 v1) v2) v1) (wim v0 v1)).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d7 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2)). Qed.
Lemma d10 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim (wim (wim v1 v2) v3) (wim v2 v3))).
Proof. exact (W_mp _ _ (W_r8 (wim v1 v2) v2 v3 v0) (d8 (wim v3 v0) v1 v2 (wim (wim v1 v2) v3) v3 v0)). Qed.
Lemma d11 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 v1) (wim (wim v0 v1) v2)) (wim v3 (wim (wim v0 v1) v2))).
Proof. exact (W_mp _ _ (d9 v0 v1 v2) (W_r8 (wim v0 v1) v3 (wim (wim v0 v1) v2) v1)). Qed.
Lemma d12 (v0 v1 : nat) : thm222 (wim v0 (wim v1 v0)).
Proof. exact (W_mp _ _ (d4 v0 (wim v1 v0) v1) (d9 v0 (wim v1 v0) v0)). Qed.
Lemma d13 (v0 v1 v2 : nat) : thm222 (wim (wim (wim v0 v1) v2) (wim v1 v2)).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d10 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2)). Qed.
Lemma d14 (v0 v1 v2 : nat) : thm222 (wim v0 (wim (wim (wim v1 v2) v1) v1)).
Proof. exact (W_mp _ _ (d4 v1 v2 (wim (wim v1 v2) v1)) (d11 (wim v1 v2) v1 v1 v0)). Qed.
Lemma d15 (v0 v1 v2 : nat) : thm222 (wim v0 (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (W_mp _ _ (W_r8 v0 v2 v1 v0) (d13 (wim v1 v0) v0 (wim (wim v0 v1) (wim v2 v1)))). Qed.
Lemma d16 (v0 v1 v2 : nat) : thm222 (wim v0 (wim v1 (wim v2 v0))).
Proof. exact (W_mp _ _ (d12 (wim v2 v0) v1) (d13 v2 v0 (wim v1 (wim v2 v0)))). Qed.
Lemma d17 (v0 v1 : nat) : thm222 (wim (wim (wim v0 v1) v0) v0).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d14 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1)). Qed.
Lemma d18 (v0 v1 v2 v3 v4 : nat) : thm222 (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) (wim v4 v0)).
Proof. exact (W_mp _ _ (d15 (wim v0 v1) v2 v3) (W_r8 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v4 v0 v1)). Qed.
Lemma d19 (v0 v1 v2 : nat) : thm222 (wim (wim v0 (wim v0 v1)) (wim v2 (wim v0 v1))).
Proof. exact (W_mp _ _ (d17 v0 v1) (W_r8 v0 v2 (wim v0 v1) v0)). Qed.
Lemma d20 (v0 v1 v2 : nat) : thm222 (wim v0 (wim (wim v1 (wim v1 v2)) (wim v1 v2))).
Proof. exact (W_mp _ _ (d19 v1 v2 (wim v1 (wim v1 v2))) (d11 v1 (wim v1 v2) (wim v1 v2) v0)). Qed.
Lemma d21 (v0 v1 : nat) : thm222 (wim (wim v0 (wim v0 v1)) (wim v0 v1)).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d20 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1)). Qed.
Lemma d22 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0).
Proof. exact (W_mp _ _ (d18 v0 v1 v2 v3 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)) (d21 (wim (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0) v0)). Qed.
Lemma d23 (v0 v1 v2 v3 v4 : nat) : thm222 (wim (wim v0 (wim (wim (wim v0 v1) v2) (wim v3 v2))) (wim v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)))).
Proof. exact (W_mp _ _ (d22 v0 v1 v2 v3) (W_r8 v0 v4 (wim (wim (wim v0 v1) v2) (wim v3 v2)) v0)). Qed.
Lemma d24 (v0 v1 v2 v3 v4 v5 : nat) : thm222 (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) (wim v5 v1)).
Proof. exact (W_mp _ _ (d23 v1 v2 v3 v4 v0) (W_r8 (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v5 v1 (wim (wim (wim v1 v2) v3) (wim v4 v3)))). Qed.
Lemma d25 (v0 v1 v2 v3 v4 : nat) : thm222 (wim (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1).
Proof. exact (W_mp _ _ (d24 v0 v1 v2 v3 v4 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1)) (d21 (wim (wim v0 (wim (wim (wim v1 v2) v3) (wim v4 v3))) v1) v1)). Qed.
Lemma d26 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 (wim v1 v2)) v1) (wim v3 v1)).
Proof. exact (W_mp _ _ (d12 (wim v1 v2) v0) (W_r8 (wim v0 (wim v1 v2)) v3 v1 v2)). Qed.
Lemma d27 (v0 v1 v2 : nat) : thm222 (wim (wim (wim v0 (wim v1 v2)) v1) v1).
Proof. exact (W_mp _ _ (d26 v0 v1 v2 (wim (wim v0 (wim v1 v2)) v1)) (d21 (wim (wim v0 (wim v1 v2)) v1) v1)). Qed.
Lemma d28 (v0 v1 v2 v3 : nat) : thm222 (wim (wim v0 (wim v1 (wim v0 v2))) (wim v3 (wim v1 (wim v0 v2)))).
Proof. exact (W_mp _ _ (d27 v1 v0 v2) (W_r8 v0 v3 (wim v1 (wim v0 v2)) v0)). Qed.
Lemma d29 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim (wim v1 v2) (wim (wim (wim v2 v3) v1) v2))).
Proof. exact (W_mp _ _ (W_r8 v1 (wim (wim v2 v3) v1) v2 v3) (d28 (wim (wim v2 v3) v1) (wim v1 v2) v2 v0)). Qed.
Lemma d30 (v0 v1 v2 : nat) : thm222 (wim (wim v0 v1) (wim (wim (wim v1 v2) v0) v1)).
Proof. exact (W_mp _ _ (W_r8 v0 v0 v0 v0) (d29 (wim (wim (wim v0 v0) v0) (wim (wim v0 v0) (wim v0 v0))) v0 v1 v2)). Qed.
Lemma d31 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) v0) (wim (wim v0 v1) (wim v2 v1))).
Proof. exact (W_mp _ _ (d15 v0 v1 v2) (d30 v0 (wim (wim v0 v1) (wim v2 v1)) v3)). Qed.
Lemma d32 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim v0 (wim v1 v2)) v3) v2) (wim v0 (wim v1 v2))).
Proof. exact (W_mp _ _ (d16 v2 v0 v1) (d30 v2 (wim v0 (wim v1 v2)) v3)). Qed.
Lemma d33 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim v0 (wim v1 v2)) v3) (wim v1 (wim v1 v2))) (wim v0 (wim v1 v2))).
Proof. exact (W_mp _ _ (d19 v1 v2 v0) (d30 (wim v1 (wim v1 v2)) (wim v0 (wim v1 v2)) v3)). Qed.
Lemma d34 (v0 v1 v2 v3 : nat) : thm222 (wim (wim v0 (wim v1 v2)) (wim (wim (wim v0 v3) v2) (wim v1 v2))).
Proof. exact (W_mp _ _ (d25 (wim v0 (wim v1 v2)) v0 v3 v2 v1) (d31 v0 (wim v1 v2) (wim (wim v0 v3) v2) v0)). Qed.
Lemma d35 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 v1) (wim v2 v3)) (wim (wim v0 v3) (wim v2 v3))).
Proof. exact (W_mp _ _ (d15 v0 v3 v2) (d34 v0 (wim v0 v3) (wim v2 v3) v1)). Qed.
Lemma d36 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim v1 (wim (wim v0 v2) (wim v3 v2)))).
Proof. exact (W_mp _ _ (d35 v0 (wim v1 (wim (wim v0 v2) (wim v3 v2))) v3 v2) (d32 v0 v1 (wim (wim v0 v2) (wim v3 v2)) (wim v3 v2))). Qed.
Lemma d37 (v0 v1 : nat) : thm222 (wim v0 (wim (wim v0 v1) v1)).
Proof. exact (W_mp _ _ (d35 v0 (wim (wim v0 v1) v1) (wim v0 v1) v1) (d33 v0 (wim v0 v1) v1 (wim (wim v0 v1) v1))). Qed.
Lemma d38 (v0 v1 v2 : nat) : thm222 (wim v0 (wim (wim (wim v1 v0) v2) v2)).
Proof. exact (W_mp _ _ (d37 (wim v1 v0) v2) (d13 v1 v0 (wim (wim (wim v1 v0) v2) v2))). Qed.
Lemma d39 (v0 v1 v2 : nat) : thm222 (wim (wim (wim v0 v1) v2) (wim (wim v0 v2) v2)).
Proof. exact (W_mp _ _ (d37 v0 v2) (d34 v0 (wim v0 v2) v2 v1)). Qed.
Lemma d40 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 v1) v2) (wim (wim (wim v3 v0) v2) v2)).
Proof. exact (W_mp _ _ (d38 v0 v3 v2) (d34 v0 (wim (wim v3 v0) v2) v2 v1)). Qed.
Lemma d41 (v0 v1 v2 v3 : nat) : thm222 (wim (wim v0 v1) (wim (wim (wim v2 (wim v0 v3)) v1) v1)).
Proof. exact (W_mp _ _ (d38 (wim v0 v3) v2 v1) (d35 v0 v3 (wim (wim v2 (wim v0 v3)) v1) v1)). Qed.
Lemma d42 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v3 (wim v0 v2))).
Proof. exact (W_mp _ _ (d39 v0 v2 v1) (W_r8 (wim (wim v0 v1) v1) v3 (wim v0 v2) v1)). Qed.
Lemma d43 (v0 v1 v2 v3 : nat) : thm222 (wim (wim v0 (wim v1 (wim v2 (wim v0 v3)))) (wim v1 (wim v2 (wim v0 v3)))).
Proof. exact (W_mp _ _ (d16 (wim v0 v3) v1 v2) (d39 v0 v3 (wim v1 (wim v2 (wim v0 v3))))). Qed.
Lemma d44 (v0 v1 v2 : nat) : thm222 (wim (wim v0 (wim (wim (wim v0 v1) v2) v2)) (wim (wim (wim v0 v1) v2) v2)).
Proof. exact (W_mp _ _ (d37 (wim v0 v1) v2) (d39 v0 v1 (wim (wim (wim v0 v1) v2) v2))). Qed.
Lemma d45 (v0 v1 v2 : nat) : thm222 (wim (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2)).
Proof. exact (W_mp _ _ (d42 v0 v1 v2 (wim (wim (wim v0 v1) v1) (wim v0 v2))) (d21 (wim (wim (wim v0 v1) v1) (wim v0 v2)) (wim v0 v2))). Qed.
Lemma d46 (v0 v1 v2 : nat) : thm222 (wim (wim (wim (wim v0 v1) (wim v0 v2)) v1) v1).
Proof. exact (W_mp _ _ (d41 v0 v1 (wim v0 v1) v2) (d44 (wim v0 v1) (wim v0 v2) v1)). Qed.
Lemma d47 (v0 v1 v2 : nat) : thm222 (wim (wim (wim (wim v0 v1) v1) v2) (wim v0 v2)).
Proof. exact (W_mp _ _ (d45 v0 v1 v2) (d35 (wim (wim v0 v1) v1) (wim v0 v2) v0 v2)). Qed.
Lemma d48 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim v0 (wim (wim v1 v2) (wim v1 v3))) v2) v2).
Proof. exact (W_mp _ _ (d46 v1 v2 v3) (d40 (wim (wim v1 v2) (wim v1 v3)) v2 v2 v0)). Qed.
Lemma d49 (v0 v1 v2 : nat) : thm222 (wim (wim v0 (wim v1 v2)) (wim (wim v1 v0) (wim v1 v2))).
Proof. exact (W_mp _ _ (d48 (wim v0 (wim v1 v2)) v1 v0 v2) (d31 v0 (wim v1 v2) (wim v1 v0) v0)). Qed.
Lemma d50 (v0 v1 v2 v3 : nat) : thm222 (wim (wim v0 v1) (wim v0 (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact (W_mp _ _ (d36 v1 v0 v2 v3) (d49 v1 v0 (wim (wim v1 v2) (wim v3 v2)))). Qed.
Lemma d51 (v0 v1 v2 v3 : nat) : thm222 (wim v0 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2)))).
Proof. exact (W_mp _ _ (d50 (wim v0 v1) v1 v2 v3) (d47 v0 v1 (wim (wim v0 v1) (wim (wim v1 v2) (wim v3 v2))))). Qed.
Lemma d52 (v0 v1 v2 : nat) : thm222 (wim (wim v0 v1) (wim (wim v1 v2) (wim v0 v2))).
Proof. exact (W_mp _ _ (d51 v0 v1 v2 v0) (d43 v0 (wim v0 v1) (wim v1 v2) v2)). Qed.
Lemma d53 (v0 v1 v2 v3 : nat) : thm222 (wim (wim (wim (wim v0 v1) (wim v2 v1)) v3) (wim (wim v2 v0) v3)).
Proof. exact (W_mp _ _ (d52 v2 v0 v1) (d52 (wim v2 v0) (wim (wim v0 v1) (wim v2 v1)) v3)). Qed.
Lemma d54 (v0 v1 v2 : nat) : thm222 (wim (wim v0 (wim v1 v2)) (wim v1 (wim v0 v2))).
Proof. exact (W_mp _ _ (d47 v1 v2 (wim v0 v2)) (d53 (wim v1 v2) v2 v0 (wim v1 (wim v0 v2)))). Qed.
Lemma d55 (v0 v1 v2 : nat) : thm222 (wim (wim v0 v1) (wim (wim v0 (wim v1 v2)) (wim v0 v2))).
Proof. exact (W_mp _ _ (d49 (wim v1 v2) v0 v2) (d53 v1 v2 v0 (wim (wim v0 (wim v1 v2)) (wim v0 v2)))). Qed.
Lemma d56 (v0 v1 v2 : nat) : thm222 (wim (wim v0 (wim v1 v2)) (wim (wim v0 v1) (wim v0 v2))).
Proof. exact (W_mp _ _ (d55 v0 v1 v2) (d54 (wim v0 v1) (wim v0 (wim v1 v2)) (wim v0 v2))). Qed.

Lemma thm_K (p q : nat) : thm222 (wim p (wim q p)).
Proof. exact (d12 p q). Qed.
Lemma thm_P (p q : nat) : thm222 (wim (wim (wim p q) p) p).
Proof. exact (d17 p q). Qed.
Lemma thm_B (p q r : nat) : thm222 (wim (wim p q) (wim (wim q r) (wim p r))).
Proof. exact (d52 p q r). Qed.
Lemma thm_S (p q r : nat) : thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof. exact (d56 p q r). Qed.
