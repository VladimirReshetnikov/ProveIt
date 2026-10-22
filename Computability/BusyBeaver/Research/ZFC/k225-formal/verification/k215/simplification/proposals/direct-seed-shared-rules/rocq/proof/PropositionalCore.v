(** One propositional proof core for the two K215 named calculi.
    Derived from Jeff's L1_LProp.v; no syntax or equality assumptions.
    See NOTICE.md and evidence/source_manifest.json for source identities. *)
Module Type PropositionalBasis.
  Parameter Formula : Type.
  Parameter Imp : Formula -> Formula -> Formula.
  Parameter Neg : Formula -> Formula.
  Parameter Pr : Formula -> Prop.
  Parameter mp : forall a b, Pr (Imp a b) -> Pr a -> Pr b.
  Parameter b1 : forall a b c,
    Pr (Imp (Imp a b) (Imp (Imp b c) (Imp a c))).
  Parameter b2 : forall a, Pr (Imp (Imp (Neg a) a) a).
  Parameter b3 : forall a b, Pr (Imp a (Imp (Neg a) b)).
End PropositionalBasis.

Module PropositionalRules (B : PropositionalBasis).
Import B.
Lemma llp5 (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Imp (Neg w0) w0) w1)).
Proof. exact (mp _ _ (b1 (Imp (Neg w0) w0) w0 w1) (b2 w0)). Qed.
Lemma llp7 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp (Neg w0) w1) w2) (Imp w0 w2)).
Proof. exact (mp _ _ (b1 w0 (Imp (Neg w0) w1) w2) (b3 w0 w1)). Qed.
Lemma llp8 (w0 : Formula) : Pr (Imp w0 w0).
Proof. exact (mp _ _ (llp7 w0 w0 w0) (b2 w0)). Qed.
Lemma llp9 (w0 w1 : Formula) : Pr (Imp (Neg (Imp w0 w0)) w1).
Proof. exact (mp _ _ (b3 (Imp w0 w0) w1) (llp8 w0)). Qed.
Lemma llp12 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp (Imp w1 w2) (Imp (Neg w0) w2))).
Proof. exact (mp _ _ (llp7 w0 w1 (Imp (Imp w1 w2) (Imp (Neg w0) w2))) (b1 (Neg w0) w1 w2)). Qed.
Lemma llp14 (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Neg (Imp w2 w2)) w1)).
Proof. exact (mp _ _ (b1 (Neg (Imp w2 w2)) w0 w1) (llp9 w2 w0)). Qed.
Lemma llp15 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp (Neg (Imp w1 w1)) w2)).
Proof. exact (mp _ _ (llp7 w0 w2 (Imp (Neg (Imp w1 w1)) w2)) (llp14 (Neg w0) w2 w1)). Qed.
Lemma llp26 (w0 w1 w2 w3 : Formula) : Pr (Imp (Imp (Imp (Neg (Imp w0 w0)) w1) w2) (Imp w3 w2)).
Proof. exact (mp _ _ (b1 w3 (Imp (Neg (Imp w0 w0)) w1) w2) (llp15 w3 w0 w1)). Qed.
Lemma llp27 (w0 w1 : Formula) : Pr (Imp w0 (Imp w1 w1)).
Proof. exact (mp _ _ (llp26 w1 (Imp w1 w1) (Imp w1 w1) w0) (b2 (Imp w1 w1))). Qed.
Lemma llp29 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp w0 w0) w1) (Imp w2 w1)).
Proof. exact (mp _ _ (b1 w2 (Imp w0 w0) w1) (llp27 w2 w0)). Qed.
Lemma llp31 (w0 w1 : Formula) : Pr (Imp w0 (Imp (Imp (Neg w1) w1) w1)).
Proof. exact (mp _ _ (llp29 w1 (Imp (Imp (Neg w1) w1) w1) w0) (llp5 w1 w1)). Qed.
Lemma llp44 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp (Imp (Neg w0) w0) w0) w1) (Imp w2 w1)).
Proof. exact (mp _ _ (b1 w2 (Imp (Imp (Neg w0) w0) w0) w1) (llp31 w2 w0)). Qed.
Lemma llp118 (w0 w1 w2 w3 : Formula) : Pr (Imp (Imp (Imp w0 w1) w2) (Imp (Imp (Imp (Neg w0) w3) w1) w2)).
Proof. exact (mp _ _ (b1 (Imp (Imp (Neg w0) w3) w1) (Imp w0 w1) w2) (llp7 w0 w3 w1)). Qed.
Lemma llp119 (w0 w1 : Formula) : Pr (Imp (Imp (Imp (Neg (Neg w0)) w1) w0) w0).
Proof. exact (mp _ _ (llp118 (Neg w0) w0 w0 w1) (b2 w0)). Qed.
Lemma llp135 (w0 w1 w2 w3 : Formula) : Pr (Imp (Imp (Imp (Imp w0 w1) (Imp (Neg w2) w1)) w3) (Imp w2 w3)).
Proof. exact (mp _ _ (b1 w2 (Imp (Imp w0 w1) (Imp (Neg w2) w1)) w3) (llp12 w2 w0 w1)). Qed.
Lemma llp136 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp w1 (Imp (Neg w0) w2))).
Proof. exact (mp _ _ (llp135 (Neg w1) w2 w0 (Imp w1 (Imp (Neg w0) w2))) (llp7 w1 w2 (Imp (Neg w0) w2))). Qed.
Lemma llp143 (w0 w1 w2 w3 : Formula) : Pr (Imp (Imp (Imp w0 (Imp (Neg w1) w2)) w3) (Imp w1 w3)).
Proof. exact (mp _ _ (b1 w1 (Imp w0 (Imp (Neg w1) w2)) w3) (llp136 w1 w0 w2)). Qed.
Lemma llp241 (w0 w1 w2 w3 : Formula) : Pr (Imp (Imp (Imp (Imp w0 w1) (Imp w2 w1)) w3) (Imp (Imp w2 w0) w3)).
Proof. exact (mp _ _ (b1 (Imp w2 w0) (Imp (Imp w0 w1) (Imp w2 w1)) w3) (b1 w2 w0 w1)). Qed.
Lemma llp244 (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 (Neg w1)) (Imp w1 (Imp w0 w2))).
Proof. exact (mp _ _ (llp241 (Neg w1) w2 w0 (Imp w1 (Imp w0 w2))) (llp7 w1 w2 (Imp w0 w2))). Qed.
Lemma llp253 (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 (Imp (Neg w1) w1)) (Imp w2 (Imp w0 w1))).
Proof. exact (mp _ _ (llp241 (Imp (Neg w1) w1) w1 w0 (Imp w2 (Imp w0 w1))) (llp44 w1 (Imp w0 w1) w2)). Qed.
Lemma llp254 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp w1 (Imp w2 w0))).
Proof. exact (mp _ _ (llp143 w2 w0 w0 (Imp w1 (Imp w2 w0))) (llp253 w2 w0 w1)). Qed.
Lemma llp255 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp w1 (Imp w2 w1))).
Proof. exact (mp _ _ (llp253 w1 (Imp w2 w1) w0) (llp254 w1 (Neg (Imp w2 w1)) w2)). Qed.
Lemma llp256 (w0 w1 : Formula) : Pr (Imp w0 (Imp w1 w0)).
Proof. exact (mp _ _ (llp255 (Imp (Imp (Neg w0) w0) w0) w0 w1) (b2 w0)). Qed.
Lemma llp261 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp w0 w1) w2) (Imp w1 w2)).
Proof. exact (mp _ _ (b1 w1 (Imp w0 w1) w2) (llp256 w1 w0)). Qed.
Lemma llp274 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp (Imp (Imp w1 (Neg w2)) w2) w2)).
Proof. exact (mp _ _ (llp253 (Imp (Imp w1 (Neg w2)) w2) w2 w0) (llp261 w1 (Neg w2) w2)). Qed.
Lemma llp275 (w0 w1 : Formula) : Pr (Imp (Imp (Imp w0 (Neg w1)) w1) w1).
Proof. exact (mp _ _ (llp274 (Imp (Imp (Neg w0) w0) w0) w0 w1) (b2 w0)). Qed.
Lemma llp300 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp (Neg (Imp w0 (Neg w1))) w2) w1) w1).
Proof. exact (mp _ _ (llp118 (Imp w0 (Neg w1)) w1 w1 w2) (llp275 w0 w1)). Qed.
Lemma llp329 (w0 w1 w2 : Formula) : Pr (Imp w0 (Imp (Imp (Imp (Imp (Neg w1) w1) w1) w2) w2)).
Proof. exact (mp _ _ (llp253 (Imp (Imp (Imp (Neg w1) w1) w1) w2) w2 w0) (llp44 w1 w2 (Neg w2))). Qed.
Lemma llp330 (w0 w1 : Formula) : Pr (Imp (Imp (Imp (Imp (Neg w0) w0) w0) w1) w1).
Proof. exact (mp _ _ (llp329 (Imp (Imp (Neg w0) w0) w0) w0 w1) (b2 w0)). Qed.
Lemma llp331 (w0 w1 : Formula) : Pr (Imp (Imp w0 (Imp (Neg w1) w1)) (Imp w0 w1)).
Proof. exact (mp _ _ (llp241 (Imp (Neg w1) w1) w1 w0 (Imp w0 w1)) (llp330 w1 (Imp w0 w1))). Qed.
Lemma llp334 (w0 w1 : Formula) : Pr (Imp (Imp (Neg w0) w1) (Imp (Imp w1 w0) w0)).
Proof. exact (mp _ _ (llp241 w1 w0 (Neg w0) (Imp (Imp w1 w0) w0)) (llp331 (Imp w1 w0) w0)). Qed.
Lemma llp335 (w0 w1 : Formula) : Pr (Imp w0 (Imp (Imp w0 w1) w1)).
Proof. exact (mp _ _ (llp261 (Neg w1) w0 (Imp (Imp w0 w1) w1)) (llp334 w1 w0)). Qed.
Lemma llp359 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp (Imp w0 w1) w1) w2) (Imp w0 w2)).
Proof. exact (mp _ _ (b1 w0 (Imp (Imp w0 w1) w1) w2) (llp335 w0 w1)). Qed.
Lemma llp360 (w0 : Formula) : Pr (Imp (Neg (Neg w0)) w0).
Proof. exact (mp _ _ (llp359 (Neg (Neg w0)) w0 w0) (llp119 w0 w0)). Qed.
Lemma llp362 (w0 w1 : Formula) : Pr (Imp (Neg w0) (Imp w0 w1)).
Proof. exact (mp _ _ (llp359 (Neg w0) w1 (Imp w0 w1)) (llp7 w0 w1 w1)). Qed.
Lemma llp364 (w0 w1 : Formula) : Pr (Imp (Neg (Imp w0 (Neg w1))) w1).
Proof. exact (mp _ _ (llp359 (Neg (Imp w0 (Neg w1))) w1 w1) (llp300 w0 w1 w1)). Qed.
Lemma llp367 (w0 : Formula) : Pr (Imp (Imp w0 (Neg w0)) (Neg w0)).
Proof. exact (mp _ _ (llp334 (Neg w0) w0) (llp360 w0)). Qed.
Lemma llp368 (w0 : Formula) : Pr (Imp w0 (Neg (Neg w0))).
Proof. exact (mp _ _ (llp7 w0 (Neg (Neg w0)) (Neg (Neg w0))) (llp367 (Neg w0))). Qed.
Lemma llp369 (w0 w1 : Formula) : Pr (Imp (Imp (Imp w0 w1) w0) w0).
Proof. exact (mp _ _ (llp334 w0 (Imp w0 w1)) (llp362 w0 w1)). Qed.
Lemma llp430 (w0 w1 : Formula) : Pr (Imp (Imp (Imp w0 (Neg (Neg w0))) w1) w1).
Proof. exact (mp _ _ (llp335 (Imp w0 (Neg (Neg w0))) w1) (llp368 w0)). Qed.
Lemma llp437 (w0 w1 : Formula) : Pr (Imp (Imp w0 (Imp w0 w1)) (Imp w0 w1)).
Proof. exact (mp _ _ (llp241 (Imp w0 w1) w1 w0 (Imp w0 w1)) (llp369 (Imp w0 w1) w1)). Qed.
Lemma llp475 (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp w0 (Neg (Neg w1)))).
Proof. exact (mp _ _ (llp241 w1 (Neg (Neg w1)) w0 (Imp w0 (Neg (Neg w1)))) (llp430 w1 (Imp w0 (Neg (Neg w1))))). Qed.
Lemma llp476 (w0 w1 : Formula) : Pr (Imp (Neg w0) (Neg (Neg (Imp w0 w1)))).
Proof. exact (mp _ _ (llp475 (Neg w0) (Imp w0 w1)) (llp362 w0 w1)). Qed.
Lemma llp483 (w0 w1 w2 : Formula) : Pr (Imp (Neg (Imp w0 w1)) (Imp (Neg w0) w2)).
Proof. exact (mp _ _ (llp244 (Neg w0) (Neg (Imp w0 w1)) w2) (llp476 w0 w1)). Qed.
Lemma llp484 (w0 w1 : Formula) : Pr (Imp (Neg (Imp w0 w1)) w0).
Proof. exact (mp _ _ (llp331 (Neg (Imp w0 w1)) w0) (llp483 w0 w1 w0)). Qed.
Lemma llp505 (w0 w1 w2 : Formula) : Pr (Imp (Imp (Imp w0 w1) w2) (Imp (Neg w0) w2)).
Proof. exact (mp _ _ (b1 (Neg w0) (Imp w0 w1) w2) (llp362 w0 w1)). Qed.
Lemma llp716 (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Imp w2 w0) (Imp w2 w1))).
Proof. exact (mp _ _ (llp359 (Imp w0 w1) (Imp w2 w1) (Imp (Imp w2 w0) (Imp w2 w1))) (llp241 w0 w1 w2 (Imp w2 w1))). Qed.
Lemma llp719 (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 (Imp w1 w2)) (Imp w1 (Imp w0 w2))).
Proof. exact (mp _ _ (llp241 (Imp w1 w2) w2 w0 (Imp w1 (Imp w0 w2))) (llp359 w1 w2 (Imp w0 w2))). Qed.
Lemma llp721 (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Imp (Neg w1) w0) w1)).
Proof. exact (mp _ _ (llp719 (Imp (Neg w1) w0) (Imp w0 w1) w1) (llp334 w1 w0)). Qed.
Lemma llp722 (w0 w1 : Formula) : Pr (Imp w0 (Imp (Imp (Neg w1) (Neg w0)) w1)).
Proof. exact (mp _ _ (llp7 w0 w1 (Imp (Imp (Neg w1) (Neg w0)) w1)) (llp721 (Neg w0) w1)). Qed.
Lemma llp724 (w0 w1 : Formula) : Pr (Imp (Imp (Neg w0) (Neg w1)) (Imp w1 w0)).
Proof. exact (mp _ _ (llp719 w1 (Imp (Neg w0) (Neg w1)) w0) (llp722 w1 w0)). Qed.
Lemma llp1317 (w0 w1 : Formula) : Pr (Imp (Imp w0 (Imp w1 (Neg w1))) (Imp w0 (Neg w1))).
Proof. exact (mp _ _ (llp716 (Imp w1 (Neg w1)) (Neg w1) w0) (llp367 w1)). Qed.
Lemma llp1549 (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Imp w1 (Neg w0)) (Neg w0))).
Proof. exact (mp _ _ (llp241 w1 (Neg w0) w0 (Imp (Imp w1 (Neg w0)) (Neg w0))) (llp1317 (Imp w1 (Neg w0)) w0)). Qed.
Lemma llp1582 (w0 w1 : Formula) : Pr (Imp (Imp w0 (Neg w1)) (Imp (Imp w1 w0) (Neg w1))).
Proof. exact (mp _ _ (llp719 (Imp w1 w0) (Imp w0 (Neg w1)) (Neg w1)) (llp1549 w1 w0)). Qed.
Lemma llp1583 (w0 w1 : Formula) : Pr (Imp w0 (Imp (Imp w1 (Neg w0)) (Neg w1))).
Proof. exact (mp _ _ (llp7 w0 (Neg w1) (Imp (Imp w1 (Neg w0)) (Neg w1))) (llp1582 (Neg w0) w1)). Qed.
Lemma llp1584 (w0 w1 : Formula) : Pr (Imp (Neg w0) (Imp (Imp w1 w0) (Neg w1))).
Proof. exact (mp _ _ (llp505 w0 (Neg w1) (Imp (Imp w1 w0) (Neg w1))) (llp1582 w0 w1)). Qed.
Lemma llp1585 (w0 w1 : Formula) : Pr (Imp (Imp w0 (Neg w1)) (Imp w1 (Neg w0))).
Proof. exact (mp _ _ (llp719 w1 (Imp w0 (Neg w1)) (Neg w0)) (llp1583 w1 w0)). Qed.
Lemma llp1586 (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Neg w1) (Neg w0))).
Proof. exact (mp _ _ (llp719 (Neg w1) (Imp w0 w1) (Neg w0)) (llp1584 w1 w0)). Qed.
Lemma llp1588 (w0 w1 : Formula) : Pr (Imp w0 (Imp w1 (Neg (Imp w0 (Neg w1))))).
Proof. exact (mp _ _ (llp359 w0 (Neg w1) (Imp w1 (Neg (Imp w0 (Neg w1))))) (llp1585 (Imp w0 (Neg w1)) w1)). Qed.
Lemma lpc_id (w0 : Formula) : Pr (Imp w0 w0).
Proof. exact (llp8 w0). Qed.
Lemma lpc_K (w0 w1 : Formula) : Pr (Imp w0 (Imp w1 w0)).
Proof. exact (llp256 w0 w1). Qed.
Lemma lpc_C (w0 w1 w2 : Formula) : Pr (Imp (Imp w0 (Imp w1 w2)) (Imp w1 (Imp w0 w2))).
Proof. exact (llp719 w0 w1 w2). Qed.
Lemma lpc_B (w0 w1 w2 : Formula) : Pr (Imp (Imp w1 w2) (Imp (Imp w0 w1) (Imp w0 w2))).
Proof. exact (llp716 w1 w2 w0). Qed.
Lemma lpc_W (w0 w1 : Formula) : Pr (Imp (Imp w0 (Imp w0 w1)) (Imp w0 w1)).
Proof. exact (llp437 w0 w1). Qed.
Lemma lpc_contra (w0 w1 : Formula) : Pr (Imp (Imp w0 w1) (Imp (Neg w1) (Neg w0))).
Proof. exact (llp1586 w0 w1). Qed.
Lemma lpc_contra2 (w0 w1 : Formula) : Pr (Imp (Imp (Neg w0) (Neg w1)) (Imp w1 w0)).
Proof. exact (llp724 w0 w1). Qed.
Lemma lpc_nn_elim (w0 : Formula) : Pr (Imp (Neg (Neg w0)) w0).
Proof. exact (llp360 w0). Qed.
Lemma lpc_nn_intro (w0 : Formula) : Pr (Imp w0 (Neg (Neg w0))).
Proof. exact (llp368 w0). Qed.
Lemma lpc_andl (w0 w1 : Formula) : Pr (Imp (Neg (Imp w0 (Neg w1))) w0).
Proof. exact (llp484 w0 (Neg w1)). Qed.
Lemma lpc_andr (w0 w1 : Formula) : Pr (Imp (Neg (Imp w0 (Neg w1))) w1).
Proof. exact (llp364 w0 w1). Qed.
Lemma lpc_andi (w0 w1 : Formula) : Pr (Imp w0 (Imp w1 (Neg (Imp w0 (Neg w1))))).
Proof. exact (llp1588 w0 w1). Qed.

End PropositionalRules.
