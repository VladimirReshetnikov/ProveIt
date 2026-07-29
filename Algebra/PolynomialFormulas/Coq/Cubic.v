From Stdlib Require Import Reals Ring Field Psatz.
From PolynomialFormulas Require Import Basic.

Open Scope R_scope.

(** Algebraic verification of Cardano's formula. *)

Module LeanProofs.
Module PolynomialFormulasCubic.

Definition cubic (a b c d x : R) : R :=
  a * x ^ 3 + b * x ^ 2 + c * x + d.

Definition monic_cubic (A B C x : R) : R :=
  x ^ 3 + A * x ^ 2 + B * x + C.

Definition depressed_cubic (p q y : R) : R := y ^ 3 + p * y + q.

Definition cubic_p (A B : R) : R := B - 3 * (A / 3) ^ 2.

Definition cubic_q (A B C : R) : R := C - B * (A / 3) + 2 * (A / 3) ^ 3.

Definition cubic_delta (p q : R) : R := (q / 2) ^ 2 + (p / 3) ^ 3.

Definition solve_cubic (a b c d u v omega : R) : R * (R * R) :=
  (u + v - (b / a) / 3,
   (omega * u + omega ^ 2 * v - (b / a) / 3,
    omega ^ 2 * u + omega * v - (b / a) / 3)).

Theorem depress_monic_cubic (A B C y : R) :
  monic_cubic A B C (y - A / 3) =
    depressed_cubic (cubic_p A B) (cubic_q A B C) y.
Proof.
  unfold monic_cubic, depressed_cubic, cubic_p, cubic_q.
  field.
Qed.

Theorem cardano_depressed (p q u v : R)
    (hu : u ^ 3 + v ^ 3 = -q) (huv : u * v = -p / 3) :
  depressed_cubic p q (u + v) = 0.
Proof.
  unfold depressed_cubic.
  assert (hp : p = -(3 * u * v)) by nra.
  assert (hq : q = -(u ^ 3 + v ^ 3)) by nra.
  rewrite hp, hq.
  ring.
Qed.

Theorem cardano_radical_pair (p q s u v : R)
    (hu : u ^ 3 = -q / 2 + s) (hv : v ^ 3 = -q / 2 - s)
    (huv : u * v = -p / 3) :
  depressed_cubic p q (u + v) = 0.
Proof.
  apply cardano_depressed; [nra | exact huv].
Qed.

Theorem cardano_discriminant_equation (p q s : R)
    (hs : s ^ 2 = cubic_delta p q) :
  (-q / 2 + s) * (-q / 2 - s) = -(p / 3) ^ 3.
Proof.
  unfold cubic_delta in hs.
  nra.
Qed.

Theorem cubic_normalization (a b c d x : R) (ha : a <> 0) :
  cubic a b c d x = a * monic_cubic (b / a) (c / a) (d / a) x.
Proof.
  unfold cubic, monic_cubic.
  field; exact ha.
Qed.

(** Scaling a compatible Cardano pair by reciprocal cube roots preserves
    its two cube equations and its product equation. *)
Lemma scale_cardano_pair (u v alpha beta U V P : R)
    (halpha : alpha ^ 3 = 1) (hbeta : beta ^ 3 = 1)
    (hab : alpha * beta = 1)
    (hu : u ^ 3 = U) (hv : v ^ 3 = V) (huv : u * v = P) :
  (alpha * u) ^ 3 = U /\
  (beta * v) ^ 3 = V /\
  (alpha * u) * (beta * v) = P.
Proof.
  repeat split.
  - replace ((alpha * u) ^ 3) with (alpha ^ 3 * u ^ 3) by ring.
    rewrite halpha, hu; ring.
  - replace ((beta * v) ^ 3) with (beta ^ 3 * v ^ 3) by ring.
    rewrite hbeta, hv; ring.
  - replace ((alpha * u) * (beta * v)) with
        ((alpha * beta) * (u * v)) by ring.
    rewrite hab, huv; ring.
Qed.

Theorem cardano_formula (a b c d s u v : R) (ha : a <> 0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / 3) :
  cubic a b c d (u + v - (b / a) / 3) = 0.
Proof.
  rewrite (cubic_normalization a b c d _ ha).
  rewrite depress_monic_cubic.
  rewrite (cardano_radical_pair _ _ s u v hu hv huv).
  ring.
Qed.

Theorem solve_cubic_correct (a b c d s u v omega : R) (ha : a <> 0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / 3)
    (homega : omega ^ 3 = 1) :
  let roots := solve_cubic a b c d u v omega in
  cubic a b c d (fst roots) = 0 /\
  cubic a b c d (fst (snd roots)) = 0 /\
  cubic a b c d (snd (snd roots)) = 0.
Proof.
  cbn [solve_cubic].
  assert (homega2 : (omega ^ 2) ^ 3 = 1).
  { replace ((omega ^ 2) ^ 3) with ((omega ^ 3) ^ 2) by ring.
    rewrite homega; ring. }
  assert (homega12 : omega * omega ^ 2 = 1).
  { replace (omega * omega ^ 2) with (omega ^ 3) by ring; exact homega. }
  assert (homega21 : omega ^ 2 * omega = 1) by (rewrite Rmult_comm; exact homega12).
  pose proof (scale_cardano_pair _ _ omega (omega ^ 2) _ _ _
    homega homega2 homega12 hu hv huv) as [hu1 [hv1 huv1]].
  pose proof (scale_cardano_pair _ _ (omega ^ 2) omega _ _ _
    homega2 homega homega21 hu hv huv) as [hu2 [hv2 huv2]].
  repeat split.
  - exact (cardano_formula a b c d s u v ha hs hu hv huv).
  - exact (cardano_formula a b c d s (omega * u) (omega ^ 2 * v)
      ha hs hu1 hv1 huv1).
  - exact (cardano_formula a b c d s (omega ^ 2 * u) (omega * v)
      ha hs hu2 hv2 huv2).
Qed.

End PolynomialFormulasCubic.
End LeanProofs.
