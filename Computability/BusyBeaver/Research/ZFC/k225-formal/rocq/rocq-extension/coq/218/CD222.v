(** Copy of rocq224/src/CD222.v (SHA256 b89848be68d211ea2dc1d01baecda9d25ca89013ade90ba78d352b45521bb178) under namespace K218F. *)
(** * CD222: implicational theorems of thm222 from the Lukasiewicz row rho8 alone.

    [DominatedCore] with the domination relation that always holds: every row is then a
    restricted row, and the core's K, Peirce, composition and S are those of thm222. *)
From K230L Require Import Codes230.
From K218F Require Import Thm222.
From K218F Require DominatedCore.

Definition mp222 a b (hab : thm222 (wim a b)) (ha : thm222 a) : thm222 b := W_mp a b ha hab.
Definition row222 a b c u (_ : True) : thm222 (rho8 a b c u) := W_r8 a b c u.

Lemma thm_K (p q : nat) : thm222 (wim p (wim q p)).
Proof.
  exact (DominatedCore.k nat wim (fun _ _ => True) (fun _ => I) (fun _ _ _ _ => I)
    (fun _ _ _ _ => I) thm222 mp222 row222 p q).
Qed.
Lemma thm_P (p q : nat) : thm222 (wim (wim (wim p q) p) p).
Proof.
  exact (DominatedCore.peirce nat wim (fun _ _ => True) (fun _ => I) (fun _ _ _ _ => I)
    (fun _ _ _ _ => I) thm222 mp222 row222 p q).
Qed.
Lemma thm_B (p q r : nat) : thm222 (wim (wim p q) (wim (wim q r) (wim p r))).
Proof.
  exact (DominatedCore.composition nat wim (fun _ _ => True) (fun _ => I) (fun _ _ _ _ => I)
    (fun _ _ _ _ => I) thm222 mp222 row222 p q r).
Qed.
Lemma thm_S (p q r : nat) : thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof.
  exact (DominatedCore.s nat wim (fun _ _ => True) (fun _ => I) (fun _ _ _ _ => I)
    (fun _ _ _ _ => I) thm222 mp222 row222 p q r).
Qed.
