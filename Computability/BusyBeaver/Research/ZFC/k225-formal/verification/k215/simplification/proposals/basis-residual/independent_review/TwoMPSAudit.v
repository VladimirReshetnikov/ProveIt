(** Independent kernel audit of the two-MP S extension.
    The three schematic premises are exactly d34, d55, and d57 of the
    maintained DominatedImplication.lean at 57541fe0cfe3af62b4cb58747d8d1d7c16b338d5.
    This checks only the extension; it does not reprove those three premises. *)
Section TwoMPS.
  Variable A : Type.
  Variable imp : A -> A -> A.
  Variable T : A -> Prop.
  Hypothesis mp : forall x y, T (imp x y) -> T x -> T y.
  Hypothesis d34 : forall p q r s,
    T (imp (imp (imp p q) (imp r s)) (imp (imp p s) (imp r s))).
  Hypothesis d55 : forall p q r,
    T (imp (imp p q) (imp (imp r p) (imp r q))).
  Hypothesis d57 : forall p q r s,
    T (imp (imp p q) (imp (imp r p) (imp s (imp r q)))).

  Theorem two_mp_S a b c :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))).
  Proof.
    exact (mp _ _
      (mp _ _
        (d34 (imp b c) c (imp a (imp b c)) (imp (imp a b) (imp a c)))
        (d57 (imp b c) c a (imp a b)))
      (d55 b c a)).
  Qed.
End TwoMPS.

Print Assumptions two_mp_S.
